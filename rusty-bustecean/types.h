struct instr {
    char opcode;
    char dst;
    char src;
    char uk[5];
    __int64 imm;
};

typedef enum {
    PUSH_IMM,
    PUSH_REG,
    POP,
    ADD,
    MOV_MEM, // mov dst, [dst - src]
    IMUL,
    IDIV,
    XOR,
    AND,
    OR,
    SHL,
    SHR,
    IO, // Unclear on specifics!
    NE_INCR, // if dst != src -> incr(rex)
    LE_INCR, // if dst <= src -> incr(rex)
    GE_INCR, // if dst >= src -> incr(rex)
    SET_REX, // rex = imm - 1
    ADD_REX, // rex = rex + imm - 1
    PUSH_SET_REX, // push rex, rex = imm - 1
    POP_REX,
    WEIRD_SHIT,
    DONE
} opcode;

struct cpu {
    long rax;
    long rbx;
    long rcx;
    long rdx;
    long rex;
    long stack_size;
    char stack[0x100]; // No idea how big
};