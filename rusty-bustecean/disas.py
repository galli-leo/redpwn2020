import sys
from pwn import *
import enum

# flag{w  rence...}
# flag{whats_the_difference...}

class Opcode(enum.Enum):
    PUSH_IMM = 0
    PUSH_REG = 1
    POP = 2
    ADD = 3
    SUB = 4
    IMUL = 5
    IDIV = 6
    XOR = 7
    AND = 8
    OR = 9
    SHL = 10
    SHR = 11
    READ = 12
    NE_SKIP = 13
    LE_SKIP = 14
    GE_SKIP = 15
    FAR_JMP = 16
    NEAR_JMP = 17
    CALL = 18
    RET = 19
    WRITE = 20
    DONE = 21

def loadfile(filename):
    log.info("Loading instructions from %s", filename)
    with open(filename, "rb") as f:
        return f.read()

class Instr:
    def __init__(self, b: bytes, rip):
        self.b = b
        self.rip = rip
        self.disas()

    def disas(self):
        instr = self.b
        self.imm = u64(instr[8:])
        self.opcode = instr[0]
        self.op = Opcode(self.opcode)
        self.dst = instr[1]
        self.src = instr[2]
        self.uk = instr[3:8]

    @property
    def dst_reg(self):
        return self.reg_name(self.dst)

    @property
    def src_reg(self):
        return self.reg_name(self.src)

    @property
    def arith(self) -> bool:
        return self.op in [Opcode.ADD, Opcode.AND, Opcode.XOR, Opcode.OR, Opcode.SHL, Opcode.SHR, Opcode.IDIV, Opcode.IMUL]

    @property
    def skip(self) -> bool:
        return self.op in [Opcode.NE_SKIP, Opcode.LE_SKIP, Opcode.GE_SKIP]

    @property
    def jmp(self) -> bool:
        return self.op in [Opcode.FAR_JMP, Opcode.NEAR_JMP]

    @property
    def syscall(self) -> bool:
        return self.op in [Opcode.READ, Opcode.WRITE]

    @property
    def call_ret(self) -> bool:
        return self.op in [Opcode.CALL, Opcode.RET]

    @property
    def stack(self) -> bool:
        return self.op in [Opcode.PUSH_IMM, Opcode.PUSH_REG, Opcode.POP]

    @property
    def mov_mem(self) -> bool:
        return self.op in [Opcode.MOV_MEM]

    @property
    def has_right(self) -> bool:
        return self.mov_mem or self.skip or self.arith

    @property
    def left_op(self) -> str:
        if self.mov_mem or self.arith or self.skip or self.op in [Opcode.PUSH_REG, Opcode.POP]:
            return self.dst_reg
        if self.jmp:
            if self.op == Opcode.FAR_JMP:
                return hex((self.imm) * 16)
            elif self.op == Opcode.NEAR_JMP:
                return hex(self.rip * 16 + (self.imm) * 16)
        if self.stack or self.call_ret:
            return hex(self.imm)
        if self.syscall:
            return self.dst_reg
        return "uk"

    @property
    def right_op(self) -> str:
        if self.mov_mem:
            return f"[{self.dst_reg} - {self.src_reg}]"
        if self.arith or self.skip:
            return self.src_reg
        return "uk"
    
    def reg_name(self, num):
        if num == 0:
            return "rax"
        if num == 1:
            return "rbx"
        if num == 2:
            return "rcx"
        if num == 3:
            return "rdx"
        if num == 4:
            return "rip"
        if num == 5:
            return "rsp"
        return "uk"

    def format(self) -> str:
        mnem = self.op.name
        ret = f"{mnem} {self.left_op}"
        if self.has_right:
            ret += ", " + self.right_op
        return ret

def disas(filename):
    contents = loadfile(filename)
    num_instr = len(contents) / 16
    log.info("have %d instructions", num_instr)
    outfile = "output.asm"
    log.info("saving to %s", outfile)
    with open(outfile, "w") as f:
        for i in range(0, len(contents), 16):
            instr = contents[i:i+16]
            ins = Instr(instr, int(i / 16))
            f.write(f"0x{i:04x}:\t\t{ins.format()}\n")

disas("vm_instr")