#
# IDAPython Xtensa processor module
#
# Based off:
# https://github.com/themadinventor/ida-xtensa
#
# Copyright (C) 2014 Fredrik Ahlberg
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along with
# this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
# Street, Fifth Floor, Boston, MA 02110-1301 USA.

import copy

try:
    from idaapi import *
except ImportError:
    class processor_t(object):
        pass
    dt_byte = dt_word = dt_dword = None
    PR_SEGS = PR_DEFSEG32 = PR_RNAMESOK = PR_ADJSEGS = PRN_HEX = PR_USE32 = 0
    ASH_HEXF3 = ASD_DECF0 = ASO_OCTF1 = ASB_BINF3 = AS_NOTAB = AS_ASCIIC = AS_ASCIIZ = 0
    CF_CALL = CF_JUMP = CF_STOP = 0
    o_void = o_reg = o_imm = o_displ = o_near = None

def ida_signed(x):
    """
    HACK around IDA's signedness problems
    """
    if (x & 0x80000000):
        return -(((~x) & 0x7FFFFFFF) + 1)
    return x
    
class Operand:
    REG     = 0
    IMM     = 1
    MEM     = 2
    RELA    = 3
    RELAL   = 4
    RELU    = 5
    MEM_INDEX = 6
    SREG    = 7

    def __init__(self, type, size, rshift, size2 = 0, rshift2 = 0, signext = False, vshift = 0, off = 0, xlate = None, dt = dt_byte, regbase = None):
        self.type = type
        self.size = size
        self.rshift = rshift
        self.size2 = size2
        self.rshift2 = rshift2
        self.signext = signext or (self.type in (Operand.RELA, Operand.RELAL, Operand.MEM))
        self.vshift = vshift
        self.off = off
        self.xlate = xlate
        self.dt = dt
        self.regbase = regbase


    def bitfield(self, opcode, size, rshift):
        val = (opcode >> rshift) & (0xffffffff >> (32 - size))
        return val

    def parse(self, op, opcode, cmd = None):
        val = self.bitfield(opcode, self.size, self.rshift)
        if self.size2:
            val |= ((opcode >> self.rshift2) & (0xffffffff >> (32-self.size2))) << self.size

        if self.signext and (val & (1 << (self.size+self.size2-1))):
            val = -((~val)&((1 << (self.size+self.size2-1))-1))-1

        val <<= self.vshift
        val += self.off

        if self.xlate:
            val = self.xlate(val)

        op.dtyp = self.dt
        if self.type == Operand.REG:
            op.type = o_reg
            op.reg = val if val < 16 else 16
        elif self.type == Operand.IMM:
            op.type = o_imm
            op.value = val
        elif self.type == Operand.MEM:
            op.type = o_mem
            op.addr = (cmd.ea+3+(val<<2))&0xfffffffc if val < 0 else (((cmd.ea+3+(val<<2))-0x40000)&0xfffffffc)
        elif self.type == Operand.MEM_INDEX:
            op.type = o_displ
            op.reg = self.bitfield(opcode, *self.regbase)
            op.addr = val
        elif self.type in (Operand.RELA, Operand.RELAL):
            op.type = o_near
            op.addr = val + cmd.ea + 4 if self.type == Operand.RELA else ((cmd.ea&0xfffffffc)+4+(val<<2))
        elif self.type == Operand.RELU:
            op.type = o_near
            op.addr = val + cmd.ea + 4
        elif self.type == Operand.SREG:
            op.type = o_reg
            op.reg = val | 0x100
        else:
            raise ValueError("unhandled operand type");

# These magic lookup tables are defined in table 3-17 and 3-18 (p.41-42) in
# Xtensa Instruction Set Architecture Reference Manual
def b4const(val):
    lut = (-1, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 16, 32, 64, 128, 256)
    return lut[val]

def b4constu(val):
    lut = (32768, 65536, 2, 3, 4, 5, 6, 7, 8, 10, 12, 16, 32, 64, 128, 256)
    return lut[val]

def movi_n(val):
    return val if val & 0x60 != 0x60 else -(0x20 - val & 0x1f)

def addin(val):
    return val if val else -1

def shimm(val):
    return 32-val

class Instr(object):

    fmt_NONE        = ()
    fmt_RRR         = (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.REG, 4, 4))
    fmt_RRR_extui   = (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 4, 8, 1, 16), Operand(Operand.IMM, 4, 20, off=1))
    fmt_RRR_sext    = (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 4, off=7))
    fmt_RRR_1imm    = (Operand(Operand.IMM, 4, 8),)
    fmt_RRR_2imm    = (Operand(Operand.IMM, 4, 8), Operand(Operand.IMM, 4, 4))
    fmt_RRR_immr    = (Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 4, 8))
    fmt_RRR_2r      = (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8))
    fmt_RRR_2rr     = (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 4))
    fmt_RRR_sll     = (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8))
    fmt_RRR_slli    = (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 4, 1, 20, xlate=shimm))
    fmt_RRR_srai    = (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 4, 8, 1, 20))
    fmt_RRR_sh      = (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 4, 8))
    fmt_RRR_ssa     = (Operand(Operand.REG, 4, 8),)
    fmt_RRR_ssai    = (Operand(Operand.IMM, 4, 8, 1, 4),)
    fmt_RRI8        = (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 8, 16, signext = True))
    fmt_RRI8_addmi  = (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 8, 16, signext = True, vshift=8, dt=dt_dword))
    fmt_RRI8_i12    = (Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 8, 16, 4, 8, dt=dt_word))
    fmt_RRI8_disp   = (Operand(Operand.REG, 4, 4), Operand(Operand.MEM_INDEX, 8, 16, vshift=0, regbase=(4, 8)))
    fmt_RRI8_disp16 = (Operand(Operand.REG, 4, 4), Operand(Operand.MEM_INDEX, 8, 16, vshift=1, dt=dt_word, regbase=(4, 8)))
    fmt_RRI8_disp32 = (Operand(Operand.REG, 4, 4), Operand(Operand.MEM_INDEX, 8, 16, vshift=2, dt=dt_dword, regbase=(4, 8)))
    fmt_RRI8_b      = (Operand(Operand.REG, 4, 8), Operand(Operand.REG, 4, 4), Operand(Operand.RELA, 8, 16))
    fmt_RRI8_bb     = (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 4, 1, 12), Operand(Operand.RELA, 8, 16))
    fmt_RI16        = (Operand(Operand.REG, 4, 4), Operand(Operand.MEM, 16, 8, dt=dt_dword))
    fmt_BRI8        = (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.RELA, 8, 16))
    fmt_BRI8_imm    = (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 12, xlate = b4const), Operand(Operand.RELA, 8, 16))
    fmt_BRI8_immu   = (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 12, xlate = b4constu), Operand(Operand.RELA, 8, 16))
    fmt_BRI12       = (Operand(Operand.REG, 4, 8), Operand(Operand.RELA, 12, 12))
    fmt_RI12S3      = (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 12, 12, vshift=3))
    fmt_CALL        = (Operand(Operand.RELA, 18, 6),)
    fmt_CALL_sh     = (Operand(Operand.RELAL, 18, 6),)
    fmt_CALLX       = (Operand(Operand.REG, 4, 8),)
    #fmt_RSR         = (Operand(Operand.IMM, 8, 8), Operand(Operand.REG, 4, 4))
    fmt_RSR         = (Operand(Operand.REG, 4, 4), Operand(Operand.SREG, 8, 8))
    
    fmt_NONEN       = ()
    fmt_RRRN        = (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.REG, 4, 4))
    fmt_RRRN_addi   = (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 4, xlate=addin))
    fmt_RRRN_2r     = (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8))
    fmt_RRRN_disp   = (Operand(Operand.REG, 4, 4), Operand(Operand.MEM_INDEX, 4, 12, vshift=2, regbase=(4, 8)))
    fmt_RI6         = (Operand(Operand.REG, 4, 8), Operand(Operand.RELU, 4, 12, 2, 4))
    fmt_RI7         = (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 12, 3, 4, xlate=movi_n))

class XtensaProcessor(processor_t):
    # IDP id ( Numbers above 0x8000 are reserved for the third-party modules)
    id = 0x8000 + 1990
    # Processor features
    flag = PR_SEGS | PR_DEFSEG32 | PR_RNAMESOK | PR_ADJSEGS | PRN_HEX | PR_USE32
    # Number of bits in a byte for code segments (usually 8)
    cnbits = 8
    # Number of bits in a byte for non-code segments (usually 8)
    dnbits = 8
    # Short processor names
    psnames = ["xtensa"]
    # Long processor names
    plnames = ["Tensilica Xtensa"]
    # Size of a segment register in bytes
    segreg_size = 0
    tbyte_size = 0

    assembler = {
        "flag": ASH_HEXF3 | ASD_DECF0 | ASO_OCTF1 | ASB_BINF3 | AS_NOTAB | AS_ASCIIC | AS_ASCIIZ,
        "uflag": 0,
        "name": "GNU assembler",
        "origin": ".org",
        "end": "end",
        "cmnt": ";",
        "ascsep": '"',
        "accsep": "'",
        "esccodes": "\"'",
        "a_ascii": ".ascii",
        "a_byte": ".byte",
        "a_word": ".short",
        "a_dword": ".int",
        "a_bss": "dfs %s",
        "a_seg": "seg",
        "a_curip": ".",
        "a_public": "",
        "a_weak": "",
        "a_extrn": ".extrn",
        "a_comdef": "",
        "a_align": ".align",
        "lbrace": "(",
        "rbrace": ")",
        "a_mod": "%",
        "a_band": "&",
        "a_bor": "|",
        "a_xor": "^",
        "a_bnot": "~",
        "a_shl": "<<",
        "a_shr": ">>",
        "a_sizeof_fmt": "size %s",
    }
    
    regNames = [
        # Core registers
        "a0",
        "a1",
        "a2",
        "a3",
        "a4",
        "a5",
        "a6",
        "a7",
        "a8",
        "a9",
        "a10",
        "a11",
        "a12",
        "a13",
        "a14",
        "a15",
        # Special registers
        "pc",
        # Fake registers
        "CS",
        "DS",
    ]
    
    regFirstSreg = regCodeSreg = len(regNames) - 2
    regLastSreg = regDataSreg = len(regNames) - 1
    
    _srIdToName = {
        3:   "sar", 
        5:   "litbase", # Extended L32R Option
        177: "epc1", # Exception Option
        178: "epc2", # High-Priority Interrupt Option
        179: "epc3", # High-Priority Interrupt Option
        180: "epc4", # High-Priority Interrupt Option
        181: "epc5", # High-Priority Interrupt Option
        182: "epc6", # High-Priority Interrupt Option
        183: "epc7", # High-Priority Interrupt Option
        192: "depc", # Exception Option
        194: "eps2", # High-Priority Interrupt Option
        195: "eps3", # High-Priority Interrupt Option
        196: "eps4", # High-Priority Interrupt Option
        197: "eps5", # High-Priority Interrupt Option
        198: "eps6", # High-Priority Interrupt Option
        199: "eps7", # High-Priority Interrupt Option
        209: "excsave1", # Exception Option
        210: "excsave2", # High-Priority Interrupt Option
        211: "excsave3", # High-Priority Interrupt Option
        212: "excsave4", # High-Priority Interrupt Option
        213: "excsave5", # High-Priority Interrupt Option
        214: "excsave6", # High-Priority Interrupt Option
        215: "excsave7", # High-Priority Interrupt Option
        226: "intset", # Interrupt Option
        227: "intclear", # Interrupt Option
        228: "intenable", # Interrupt Option
        230: "ps",
        231: "vecbase", # Relocatable Vector Option
        232: "exccause", # Exception Option
        235: "prid", # Processor ID Option
        238: "excvaddr", # Exception Option
    }

    # Instruction definintions
    instruc = [
#       { "name": "ill",         "opc": 0x000000, "mask": 0xffffff, "fmt": Instr.fmt_NONE, "feature": 0 },
        
        # Core Instruction Set
        { "name": "and",         "opc": 0x100000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "or",          "opc": 0x200000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "xor",         "opc": 0x300000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "add",         "opc": 0x800000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "addx2",       "opc": 0x900000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": 0 },
        { "name": "addx2",       "opc": 0x900000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": 0 },
        { "name": "addx4",       "opc": 0xa00000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "addx8",       "opc": 0xb00000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": 0 },
        { "name": "addx8",       "opc": 0xb00000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": 0 },
        { "name": "sub",         "opc": 0xc00000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "subx2",       "opc": 0xd00000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "subx4",       "opc": 0xe00000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "subx8",       "opc": 0xf00000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "slli",        "opc": 0x010000, "mask": 0xef000f, "fmt": Instr.fmt_RRR_slli, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "srai",        "opc": 0x210000, "mask": 0xef000f, "fmt": Instr.fmt_RRR_srai, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "srli",        "opc": 0x410000, "mask": 0xff000f, "fmt": Instr.fmt_RRR_sh, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "xsr",         "opc": 0x610000, "mask": 0xff000f, "fmt": Instr.fmt_RSR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 },
        { "name": "src",         "opc": 0x810000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "srl",         "opc": 0x910000, "mask": 0xff0f0f, "fmt": Instr.fmt_RRR_2rr, "feature": CF_CHG1 | CF_USE1 | CF_USE2 },
        { "name": "sll",         "opc": 0xa10000, "mask": 0xff00ff, "fmt": Instr.fmt_RRR_sll, "feature": CF_CHG1 | CF_USE1 | CF_USE2 },
        { "name": "sra",         "opc": 0xb10000, "mask": 0xff0f0f, "fmt": Instr.fmt_RRR_2rr, "feature": CF_CHG1 | CF_USE1 | CF_USE2 },
        { "name": "rsr",         "opc": 0x030000, "mask": 0xff000f, "fmt": Instr.fmt_RSR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 },
        { "name": "wsr",         "opc": 0x130000, "mask": 0xff000f, "fmt": Instr.fmt_RSR, "feature": CF_USE1 | CF_USE2 },
        { "name": "moveqz",      "opc": 0x830000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "movnez",      "opc": 0x930000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "movltz",      "opc": 0xa30000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "movgez",      "opc": 0xb30000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        
        { "name": "jx",          "opc": 0x0000a0, "mask": 0xfff0ff, "fmt": Instr.fmt_CALLX, "feature": CF_STOP | CF_JUMP | CF_USE1 },
        { "name": "callx0",      "opc": 0x0000c0, "mask": 0xfff0ff, "fmt": Instr.fmt_CALLX, "feature": CF_CALL | CF_JUMP | CF_USE1 },
        
        { "name": "ssr",         "opc": 0x400000, "mask": 0xfff0ff, "fmt": Instr.fmt_RRR_ssa, "feature": CF_USE1 },
        { "name": "ssl",         "opc": 0x401000, "mask": 0xfff0ff, "fmt": Instr.fmt_RRR_ssa, "feature": CF_USE1 },
        { "name": "ssa8l",       "opc": 0x402000, "mask": 0xfff0ff, "fmt": Instr.fmt_RRR_ssa, "feature": CF_USE1 },
        { "name": "ssa8b",       "opc": 0x403000, "mask": 0xfff0ff, "fmt": Instr.fmt_RRR_ssa, "feature": CF_USE1 },
        { "name": "ssai",        "opc": 0x404000, "mask": 0xfff0ef, "fmt": Instr.fmt_RRR_ssai, "feature": CF_USE1 },
        { "name": "neg",         "opc": 0x600000, "mask": 0xff0f0f, "fmt": Instr.fmt_RRR_2rr, "feature": CF_CHG1 | CF_USE1 | CF_USE2 },
        { "name": "abs",         "opc": 0x600100, "mask": 0xff0f0f, "fmt": Instr.fmt_RRR_2rr, "feature": CF_CHG1 | CF_USE1 | CF_USE2 },
        { "name": "extui",       "opc": 0x040000, "mask": 0x0e000f, "fmt": Instr.fmt_RRR_extui, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 | CF_USE4 },
        { "name": "isync",       "opc": 0x002000, "mask": 0xffffff, "fmt": Instr.fmt_NONE, "feature": 0 },
        { "name": "rsync",       "opc": 0x002010, "mask": 0xffffff, "fmt": Instr.fmt_NONE, "feature": 0 },
        { "name": "esync",       "opc": 0x002020, "mask": 0xffffff, "fmt": Instr.fmt_NONE, "feature": 0 },
        { "name": "dsync",       "opc": 0x002030, "mask": 0xffffff, "fmt": Instr.fmt_NONE, "feature": 0 },
        { "name": "memw",        "opc": 0x0020c0, "mask": 0xffffff, "fmt": Instr.fmt_NONE, "feature": 0 },
        { "name": "extw",        "opc": 0x0020d0, "mask": 0xffffff, "fmt": Instr.fmt_NONE, "feature": 0 },
        { "name": "nop",         "opc": 0x0020f0, "mask": 0xffffff, "fmt": Instr.fmt_NONE, "feature": 0 },
        { "name": "break",       "opc": 0x004000, "mask": 0xfff00f, "fmt": Instr.fmt_RRR_2imm, "feature": 0 },
        { "name": "ret",         "opc": 0x000080, "mask": 0xffffff, "fmt": Instr.fmt_NONE, "feature": CF_STOP },
        
        { "name": "l32r",        "opc": 0x000001, "mask": 0x00000f, "fmt": Instr.fmt_RI16, "feature": CF_USE1 | CF_USE2 },
        
        { "name": "l8ui",        "opc": 0x000002, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_disp, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "l16ui",       "opc": 0x001002, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_disp16, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "l32i",        "opc": 0x002002, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_disp32, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "s8i",         "opc": 0x004002, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_disp, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "s16i",        "opc": 0x005002, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_disp16, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "s32i",        "opc": 0x006002, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_disp32, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "l16si",       "opc": 0x009002, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_disp16, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "movi",        "opc": 0x00a002, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_i12, "feature": CF_CHG1 | CF_USE1 | CF_USE2 },
        { "name": "addi",        "opc": 0x00c002, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "addmi",       "opc": 0x00d002, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_addmi, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },

        { "name": "call0",       "opc": 0x000005, "mask": 0x00003f, "fmt": Instr.fmt_CALL_sh, "feature": CF_CALL | CF_USE1 },
        
        { "name": "j",           "opc": 0x000006, "mask": 0x00003f, "fmt": Instr.fmt_CALL, "feature": CF_STOP | CF_USE1 },
        { "name": "beqz",        "opc": 0x000016, "mask": 0x0000ff, "fmt": Instr.fmt_BRI12, "feature": CF_USE1 | CF_USE2 },
        { "name": "beqi",        "opc": 0x000026, "mask": 0x0000ff, "fmt": Instr.fmt_BRI8_imm, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bnez",        "opc": 0x000056, "mask": 0x0000ff, "fmt": Instr.fmt_BRI12, "feature": CF_USE1 | CF_USE2 },
        { "name": "bnei",        "opc": 0x000066, "mask": 0x0000ff, "fmt": Instr.fmt_BRI8_imm, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bltz",        "opc": 0x000096, "mask": 0x0000ff, "fmt": Instr.fmt_BRI12, "feature": CF_USE1 | CF_USE2 },
        { "name": "blti",        "opc": 0x0000a6, "mask": 0x0000ff, "fmt": Instr.fmt_BRI8_imm, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bltui",       "opc": 0x0000b6, "mask": 0x0000ff, "fmt": Instr.fmt_BRI8_immu, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bgez",        "opc": 0x0000d6, "mask": 0x0000ff, "fmt": Instr.fmt_BRI12, "feature": CF_USE1 | CF_USE2 },
        { "name": "bgei",        "opc": 0x0000e6, "mask": 0x0000ff, "fmt": Instr.fmt_BRI8_imm, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bgeui",       "opc": 0x0000f6, "mask": 0x0000ff, "fmt": Instr.fmt_BRI8_immu, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        
        { "name": "bnone",       "opc": 0x000007, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_b, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "beq",         "opc": 0x001007, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_b, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "blt",         "opc": 0x002007, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_b, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bltu",        "opc": 0x003007, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_b, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "ball",        "opc": 0x004007, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_b, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bbc",         "opc": 0x005007, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_b, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bbci",        "opc": 0x006007, "mask": 0x00e00f, "fmt": Instr.fmt_RRI8_bb, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bany",        "opc": 0x008007, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_b, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bne",         "opc": 0x009007, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_b, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bge",         "opc": 0x00a007, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_b, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bgeu",        "opc": 0x00b007, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_b, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bnall",       "opc": 0x00c007, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_b, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bbs",         "opc": 0x00d007, "mask": 0x00f00f, "fmt": Instr.fmt_RRI8_b, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "bbsi",        "opc": 0x00e007, "mask": 0x00e00f, "fmt": Instr.fmt_RRI8_bb, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        
        # Exception Option
        { "name": "rfe",         "opc": 0x003000, "mask": 0xffffff, "fmt": Instr.fmt_NONE, "feature": CF_STOP },
        
        # Region Translation / MMU Option
        { "name": "wdtlb",       "opc": 0x50e000, "mask": 0xfff00f, "fmt": Instr.fmt_RRR_2r, "feature": CF_USE1 | CF_USE2 },
        { "name": "witlb",       "opc": 0x506000, "mask": 0xfff00f, "fmt": Instr.fmt_RRR_2r, "feature": CF_USE1 | CF_USE2 },
        
        # Interrupt Option
        { "name": "rfi",         "opc": 0x003010, "mask": 0xfff0ff, "fmt": Instr.fmt_RRR_1imm, "feature": CF_STOP | CF_USE1 },
        { "name": "rsil",        "opc": 0x006000, "mask": 0xfff00f, "fmt": Instr.fmt_RRR_immr, "feature": CF_USE1 | CF_USE2 },
        { "name": "waiti",       "opc": 0x007000, "mask": 0xfff0ff, "fmt": Instr.fmt_RRR_1imm, "feature": CF_USE1 },
    
        # 16-bit Integer Multiply Option
        { "name": "mul16s",      "opc": 0xd10000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "mul16u",      "opc": 0xc10000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        
        # 32-bit Integer Multiply Option
        { "name": "mull",        "opc": 0x820000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "muluh",       "opc": 0xa20000, "mask": 0xff000f, "fmt": Instr.fmt_RRR, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        
        # Miscellaneous Operations Option
        { "name": "nsa",         "opc": 0x40e000, "mask": 0xfff00f, "fmt": Instr.fmt_RRR_2r, "feature": CF_CHG1 | CF_USE1 | CF_USE2 },
        { "name": "nsau",        "opc": 0x40f000, "mask": 0xfff00f, "fmt": Instr.fmt_RRR_2r, "feature": CF_CHG1 | CF_USE1 | CF_USE2 },
        { "name": "sext",        "opc": 0x230000, "mask": 0xff000f, "fmt": Instr.fmt_RRR_sext, "feature": CF_CHG1 | CF_USE1 | CF_USE2 | CF_USE3 },
        
        # Windowed Register Option
        { "name": "callx4",      "opc": 0x0000d0, "mask": 0xfff0ff, "fmt": Instr.fmt_CALLX, "feature": CF_CALL | CF_JUMP | CF_USE1 },
        { "name": "callx8",      "opc": 0x0000e0, "mask": 0xfff0ff, "fmt": Instr.fmt_CALLX, "feature": CF_CALL | CF_JUMP | CF_USE1 },
        { "name": "callx12",     "opc": 0x0000f0, "mask": 0xfff0ff, "fmt": Instr.fmt_CALLX, "feature": CF_CALL | CF_JUMP | CF_USE1 },
        { "name": "call4",       "opc": 0x000015, "mask": 0x00003f, "fmt": Instr.fmt_CALL_sh, "feature": CF_CALL | CF_USE1 },
        { "name": "call8",       "opc": 0x000025, "mask": 0x00003f, "fmt": Instr.fmt_CALL_sh, "feature": CF_CALL | CF_USE1 },
        { "name": "call12",      "opc": 0x000035, "mask": 0x00003f, "fmt": Instr.fmt_CALL_sh, "feature": CF_CALL | CF_USE1 },
        { "name": "entry",       "opc": 0x000036, "mask": 0x0000ff, "fmt": Instr.fmt_RI12S3, "feature": CF_USE1 | CF_USE2 },
        { "name": "retw.n",      "opc": 0x00f01d, "mask": 0xffffff, "fmt": Instr.fmt_NONEN, "feature": CF_STOP },

        # Code Density Option
        { "name": "l32i.n",      "opc": 0x000008, "mask": 0xff000f, "fmt": Instr.fmt_RRRN_disp, "feature": CF_USE1 | CF_USE2 },
        { "name": "s32i.n",      "opc": 0x000009, "mask": 0xff000f, "fmt": Instr.fmt_RRRN_disp, "feature": CF_USE1 | CF_USE2 },
        { "name": "add.n",       "opc": 0x00000a, "mask": 0xff000f, "fmt": Instr.fmt_RRRN, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "addi.n",      "opc": 0x00000b, "mask": 0xff000f, "fmt": Instr.fmt_RRRN_addi, "feature": CF_USE1 | CF_USE2 | CF_USE3 },
        { "name": "movi.n",      "opc": 0x00000c, "mask": 0xff008f, "fmt": Instr.fmt_RI7, "feature": CF_USE1 | CF_USE2 },
        { "name": "beqz.n",      "opc": 0x00008c, "mask": 0xff00cf, "fmt": Instr.fmt_RI6, "feature": CF_USE1 | CF_USE2 },
        { "name": "bnez.n",      "opc": 0x0000cc, "mask": 0xff00cf, "fmt": Instr.fmt_RI6, "feature": CF_USE1 | CF_USE2 },
        { "name": "mov.n",       "opc": 0x00000d, "mask": 0xfff00f, "fmt": Instr.fmt_RRRN_2r, "feature": CF_USE1 | CF_USE2 },
        { "name": "ret.n",       "opc": 0x00f00d, "mask": 0xffffff, "fmt": Instr.fmt_NONEN, "feature": CF_STOP },
        { "name": "break.n",     "opc": 0x00f02d, "mask": 0xfff0ff, "fmt": Instr.fmt_RRRN, "feature": 0 },
        { "name": "nop.n",       "opc": 0x00f03d, "mask": 0xffffff, "fmt": Instr.fmt_NONEN, "feature": 0 },
    ]
    instruc_start = 0
    instruc_end = len(instruc)

    def __init__(self):
        processor_t.__init__(self)
        # Analysis options:
        self._tighten_enabled = True

    def _mnem_to_id(self, mnem):
        for i in xrange(XtensaProcessor.instruc_end):
            instr = self._instr_from_id(i)
            if instr["name"] == mnem:
                return i
        return None
        
    def _instr_from_id(self, i):
        return XtensaProcessor.instruc[i]

    def _tighten(self):
        """Undoes some of relaxation done by `as`"""
        instr = self._instr_from_id(self.cmd.itype)
        
        if instr["name"] == "l32r":
            # Transform l32r into movi
            self.cmd.itype = self._mnem_to_id("movi")
            addr = self.cmd[1].addr
            ua_dodata2(0, addr, dt_dword)
            self.cmd[1].type = o_imm
            self.cmd[1].value = get_long(addr)

    def _trace_sp(self):
        """Trace SP flow"""
        func = get_func(self.cmd.ea)
        if not func:
            return
        instr = self._instr_from_id(self.cmd.itype)
        if instr["name"] in ("addi", "addmi") and self.cmd[0].reg == 1 and self.cmd[1].reg == 1:
            offset = ida_signed(self.cmd[2].value)
            add_auto_stkpnt2(func, self.cmd.ea + self.cmd.size, offset)
        # TODO: movi/sub + movi/add.n

    def _make_stkvar(self, op):
        """Turn the operand into a stack variable reference"""
        func = get_func(self.cmd.ea)
        if not func:
            return
        if ua_stkvar2(op, op.addr, STKVAR_VALID_SIZE):
            op_stkvar(self.cmd.ea, op.n)

    # IDA callbacks

    def ana(self):
        """Analyse and decode the current instruction into `cmd`"""

        # Determine how long the opcode is
        if get_full_byte(self.cmd.ea) & 0x08:
            self.cmd.size =  2
        else:
            self.cmd.size =  3
        
        # Fetch the opcode
        opcode = get_full_byte(self.cmd.ea + 0)
        opcode |= get_full_byte(self.cmd.ea + 1) << 8
        if self.cmd.size == 3:
            opcode |= get_full_byte(self.cmd.ea + 2) << 16
            
        # Find the corresponding insn
        for i in xrange(XtensaProcessor.instruc_end):
            instr = self._instr_from_id(i)
            if (opcode & instr["mask"]) == instr["opc"]:
                self.cmd.itype = i
                break
        else:
            # Not found; fail the decoding.
            return 0
            
        # Parse the operands
        operands = [self.cmd[i] for i in range(6)]
        for o in operands:
            o.type = o_void
        for op, fmt in zip(operands, instr["fmt"]):
            fmt.parse(op, opcode, self.cmd)
        
        # Undo some relaxation done by `as`
        # Ref: http://web.mit.edu/rhel-doc/3/rhel-as-en-3/xtensa-relaxation.html
        if self._tighten_enabled:
            self._tighten()

        # Done
        return self.cmd.size

    def _emu_op(self, op):
        idef = self._instr_from_id(self.cmd.itype)
        if op.type == o_mem:
            ua_dodata2(0, op.addr, op.dtyp)
            ua_add_dref(0, op.addr, dr_R)
        elif op.type == o_near:
            features = self.cmd.get_canon_feature()
            if features & CF_CALL:
                fl = fl_CN
            else:
                fl = fl_JN
            ua_add_cref(0, op.addr, fl)
        elif op.type == o_displ:
            if may_create_stkvars():
                # Currently, all these operands refer to the stack
                if op.reg == 1:
                    self._make_stkvar(op)
        elif op.type == o_imm:
            if may_create_stkvars():
                # addi aX, a1, imm
                if idef["name"] == "addi" and self.cmd[0].reg != 1 and self.cmd[1].reg == 1:
                    self._make_stkvar(op)

    def emu(self):
        """
        Emulate instruction, create cross-references, 
        plan to analyze subsequent instructions, modify flags etc. 
        Upon entrance to this function all information about 
        the instruction is in 'cmd' structure.

        If zero is returned, the kernel will delete the instruction.
        """
                
        feature = self.cmd.get_canon_feature()
        # Handle operands
        if feature & CF_USE1:
            self._emu_op(self.cmd[0])
        if feature & CF_USE2:
            self._emu_op(self.cmd[1])
        if feature & CF_USE3:
            self._emu_op(self.cmd[2])
        if feature & CF_USE4:
            self._emu_op(self.cmd[3])

        # Handle features
        if feature & CF_JUMP:
            QueueMark(Q_jumps, self.cmd.ea)
        flow = not ((feature & CF_STOP) or (False))
        if flow:
            ua_add_cref(0, self.cmd.ea + self.cmd.size, fl_F)

        # Handle SP changes
        if may_trace_sp():
            if flow:
                self._trace_sp()
            else:
                recalc_spd(self.cmd.ea)

        return True

    def outop(self, op):
        """Generate text representation of an instructon operand"""

        if op.type == o_reg:
            if op.reg & 0x100:
                # Handling for special registers
                sfrId = op.reg & 0xFF
                try:
                    out_register(self._srIdToName[sfrId])
                except KeyError:
                    OutLong(sfrId, 10)
            else:
                out_register(self.regNames[op.reg])
            
        elif op.type == o_imm:
            instr = self._instr_from_id(self.cmd.itype)
            if instr["name"] in ("extui", "bbci", "bbsi", "slli", "srli", "srai", "ssai"):
                # bit numbers/shifts are always decimal
                OutLong(op.value, 10)
            elif instr["name"] in ("addi", "addmi", "addi.n"):
                # immediate values for these are always signed
                OutValue(op, OOFW_IMM|OOF_SIGNED)
            else:
                OutValue(op, OOFW_IMM)
                
        elif op.type in (o_near, o_mem):
            ok = out_name_expr(op, op.addr, BADADDR)
            if not ok:
                out_tagon(COLOR_ERROR)
                OutLong(op.addr, 16)
                out_tagoff(COLOR_ERROR)
                QueueMark(Q_noName, self.cmd.ea)
                
        elif op.type == o_displ:
            out_register(self.regNames[op.reg])
            OutLine(", ")
            OutValue(op, OOF_ADDR)
            
        else:
            return False
        return True

    def out(self):
        """Generate text representation of an instruction in the `cmd` structure"""
        
        buf = init_output_buffer(1024)
        instr = self._instr_from_id(self.cmd.itype)

        # Output the instruction's mnemonic
        OutMnem()
        # Output each operand
        for i in range(6):
            if self.cmd[i].type == o_void:
                break

            if i > 0:
                out_symbol(',')
            OutChar(' ')
            out_one_operand(i)

        term_output_buffer()
        cvar.gl_comm = 1
        MakeLine(buf)

    def is_sp_based(self, op):
        """IDA HACK: check if `op` is SP or FP based"""
        return 1

def PROCESSOR_ENTRY():
    return XtensaProcessor()
# EOF
