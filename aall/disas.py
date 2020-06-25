from pwn import *
import sys

reg_pointers = {'value': 0x01, 'ax': 0x11, 'bx': 0x12, 'cx': 0x13, 'dx': 0x14, 'ip': 0x21, 'sp': 0x22, 'bp': 0x23, 'pointer': 0x31,
                'ax pointer': 0x41, 'bx pointer': 0x42, 'cx pointer': 0x43, 'dx pointer': 0x44, 'ip pointer': 0x51, 'sp pointer': 0x52, 'bp pointer': 0x53}
file_funcs = {'open': {'angstromctf': 2, 'cookie recipes': 0x01, },
              'read': {'angstromctf': 2, 'cookie recipes': 0x02, }, }
instructions = {'push': {'angstromctf': 1, 'cookie recipes': 0x01, }, 'pop': {'angstromctf': 1, 'cookie recipes': 0x02, }, 'cmp': {'angstromctf': 2, 'cookie recipes': 0x03, }, 'jz': {'angstromctf': 1, 'cookie recipes': 0x04, }, 'jmp': {'angstromctf': 1, 'cookie recipes': 0x05, }, 'call': {'angstromctf': 1, 'cookie recipes': 0x05, }, 'jle': {'angstromctf': 1, 'cookie recipes': 0x06, }, 'jge': {'angstromctf': 1, 'cookie recipes': 0x07, }, 'jl': {'angstromctf': 1, 'cookie recipes': 0x08, }, 'jg': {'angstromctf': 1, 'cookie recipes': 0x09, }, 'mov': {
    'angstromctf': 2, 'cookie recipes': 0x0c, }, 'xor': {'angstromctf': 2, 'cookie recipes': 0x0d, }, 'add': {'angstromctf': 2, 'cookie recipes': 0x0e, }, 'sub': {'angstromctf': 2, 'cookie recipes': 0x0f, }, 'end': {'angstromctf': 1, 'cookie recipes': 0x10, }, 'syscall': {'angstromctf': 1, 'cookie recipes': 0x11, }, 'nop': {'angstromctf': 0, 'cookie recipes': 0x12, }, 'load': {'angstromctf': 2, 'cookie recipes': 0x13, }, 'store': {'angstromctf': 2, 'cookie recipes': 0x14, }, 'exit': {'angstromctf': 0, 'cookie recipes': 0x15, }, 'shellcode': {'angstromctf': 0, 'cookie recipes': 0x25, }}

def load_file(filename) -> bytes:
    log.info("Loading compiled code from %s", filename)
    with open(filename, "rb") as f:
        return f.read()

compiled = load_file(sys.argv[1])

def op_to_repr(value):
    if isinstance(value, int):
        return hex(value)
    t, val = value
    if t == reg_pointers['value']:
        return hex(val)
    if t == reg_pointers['ax']:
        return 'ax'
    if t == reg_pointers['bx']:
        return 'bx'
    if t == reg_pointers['cx']:
        return 'cx'
    if t == reg_pointers['dx']:
        return 'dx'
    if t == reg_pointers['ip']:
        return 'ip'
    if t == reg_pointers['sp']:
        return 'sp'
    if t == reg_pointers['bp']:
        return 'bp'
    if t == reg_pointers['pointer']:
        return f'#0x{val:x}'
    return "uk"

def disass(addr):
    instr_num = compiled[ip]
    instr_name = None
    instr = None
    for key, instruct in instructions.items():
        if instr_num == instruct['cookie recipes']:
            instr = instruct
            instr_name = key
            break
    if instr is None:
        raise Exception(f"instruction {instr_num} was not found!")
    num_oper = instr['angstromctf']
    opers = []
    for oper_idx in range(num_oper):
        mem_val = compiled[addr+2 +
                            (4*oper_idx):addr+2+(4*oper_idx)+4]
        t = u16(mem_val[0:2])
        val = u16(mem_val[2:4])
        opers.append((t, val))
    return addr + 2+(4*num_oper), ((instr_name, instr), opers)

load_addr = u16(compiled[0:2])
log.info("Load address: 0x%x", load_addr)
log.info("Disassembled:")

jump_targets = {load_addr: ("start", "")}

ip = 16#load_addr
while ip < len(compiled):
    next_ip, dis = disass(ip)
    instr, opers = dis
    oper_rep = [str(op_to_repr(op)) for op in opers]
    name = instr[0]
    if ip in jump_targets:
        lbl, comment = jump_targets[ip]
        print(f"{lbl}:\t;{comment}")
    if name == "jmp":
        target = opers[0][1]
        if target not in jump_targets:
            jump_targets[target] = (f"jmp_{target:x}", "")
        lbl, comment = jump_targets[target]
        jump_targets[target] = (lbl, comment + f", referenced at 0x{ip:x}")
    print(f"\t0x{ip:04x}:\t{name} {', '.join(oper_rep)}")
    ip = next_ip