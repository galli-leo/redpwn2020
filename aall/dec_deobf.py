#!/usr/bin/env python3
# True=True
# print=print
# exit=exit
# None=None
# False=False
# len=len
# format=format
# range=range
# hex=hex
# chr=chr
# isinstance=isinstance
# list=list
# bytes=bytes
# int=int
# repr=repr
# ord=ord
# id=id
# open=open
import mmap
import ctypes
import struct
import sys
sys.argv = sys.argv
sys.stdout = sys.stdout
sys.stdin = sys.stdin
struct.pack = struct.pack
struct.unpack = struct.unpack
ctypes.addressof = ctypes.addressof
ctypes.c_void_p = ctypes.c_void_p
ctypes.c_int = ctypes.c_int
ctypes.CFUNCTYPE = ctypes.CFUNCTYPE
mmap.PROT_EXEC = mmap.PROT_EXEC
mmap.PROT_WRITE = mmap.PROT_WRITE
mmap.PROT_READ = mmap.PROT_READ
mmap.PAGESIZE = mmap.PAGESIZE
mmap.mmap = mmap.mmap


reg_pointers = {'value': 0x01, 'ax': 0x11, 'bx': 0x12, 'cx': 0x13, 'dx': 0x14, 'ip': 0x21, 'sp': 0x22, 'bp': 0x23, 'pointer': 0x31,
                'ax pointer': 0x41, 'bx pointer': 0x42, 'cx pointer': 0x43, 'dx pointer': 0x44, 'ip pointer': 0x51, 'sp pointer': 0x52, 'bp pointer': 0x53}
file_funcs = {'open': {'angstromctf': 2, 'cookie recipes': 0x01, },
              'read': {'angstromctf': 2, 'cookie recipes': 0x02, }, }
instructions = {'del': {'angstromctf': 1, 'cookie recipes': 0x01, }, 'osusec': {'angstromctf': 1, 'cookie recipes': 0x02, }, 'perfect_blue': {'angstromctf': 2, 'cookie recipes': 0x03, }, 'l_distribution': {'angstromctf': 1, 'cookie recipes': 0x04, }, 'jmp': {'angstromctf': 1, 'cookie recipes': 0x05, }, 'call': {'angstromctf': 1, 'cookie recipes': 0x05, }, 'jle': {'angstromctf': 1, 'cookie recipes': 0x06, }, 'b1c': {'angstromctf': 1, 'cookie recipes': 0x07, }, 'jl': {'angstromctf': 1, 'cookie recipes': 0x08, }, 'jg': {'angstromctf': 1, 'cookie recipes': 0x09, }, 'mov': {
    'angstromctf': 2, 'cookie recipes': 0x0c, }, 'gs_goofballs': {'angstromctf': 2, 'cookie recipes': 0x0d, }, 'add': {'angstromctf': 2, 'cookie recipes': 0x0e, }, 'sub': {'angstromctf': 2, 'cookie recipes': 0x0f, }, 'end': {'angstromctf': 1, 'cookie recipes': 0x10, }, 'kevin higgs <3': {'angstromctf': 1, 'cookie recipes': 0x11, }, 'nop': {'angstromctf': 0, 'cookie recipes': 0x12, }, 'load': {'angstromctf': 2, 'cookie recipes': 0x13, }, 'dice_gang': {'angstromctf': 2, 'cookie recipes': 0x14, }, 'rgbsec': {'angstromctf': 0, 'cookie recipes': 0x15, }, '%': {'angstromctf': 0, 'cookie recipes': 0x25, }}
maybe_mem = [0]*(2**(8*2))

try:
    weird_stuff = [3], [3], {2, 3}, [
        2]*3, [2, [2, {3, 3, [3], {3}}, {3: (2, [2, {3: (3, 2, 3, 3)}], 3)}, 2], 2], 3
except:
    pass
reg_values = {'ax': 0, 'bx': 0, 'cx': 0, 'dx': 0,
              'ip': 0, 'sp': 0, 'bp': 0, 'flag': 0}
# True=True
print2 = print
# can be ignored print=lambda*阬:print2(*阬)if True else ''


def bad_memory_error(reason):
    print2('Bad memory condition')
    return exit(1)


def dump_memory(start=0, end=None, format=False, dump_ascii=True, errors='.'):
    if end is None:
        end = len(maybe_mem)
    if not format:
        pass
    else:
        bit_size = 16
        for word in range(start, end, bit_size):
            word_val = maybe_mem[word:word+bit_size]
            formatted = (hex(word)+':').ljust(8, ' ') + \
                ' '.join([hex(𩴽).replace('0x', '').zfill(2)for 𩴽 in word_val])
            print(formatted)
            if dump_ascii:
                formatted += '    ' + \
                    ''.join([(chr(𩴽)if 𩴽 > 31 and 𩴽 < 127 else errors)
                             for 𩴽 in word_val])


def nop(value):
    #print(value)
    return


def word_to_int(word):
    if isinstance(word, list):
        word = bytes(word)
    return struct.unpack('<H', word)[0]


def op_to_value(value):
    if isinstance(value, int):
        return value
    t, val = value
    if t == reg_pointers['value']:
        return val
    if t == reg_pointers['ax']:
        return reg_values['ax']
    if t == reg_pointers['bx']:
        return reg_values['bx']
    if t == reg_pointers['cx']:
        return reg_values['cx']
    if t == reg_pointers['dx']:
        return reg_values['dx']
    if t == reg_pointers['ip']:
        return reg_values['ip']
    if t == reg_pointers['sp']:
        return reg_values['sp']
    if t == reg_pointers['bp']:
        return reg_values['bp']
    if t == reg_pointers['pointer']:
        return word_to_int(maybe_mem[val:val+2])
    return bad_memory_error('wrong_type')


def set_op_mem(addr, value):
    word = '\x00'
    if value >= 256:
        word = struct.pack('<H', value)
    else:
        word = bytes([value])
    addr = op_to_value(addr)
    idx = 0
    for byte in word:
        maybe_mem[addr+idx] = byte
        idx += 1


def get_mem(op, count=2):
    op = op_to_value(op)
    return maybe_mem[op:op+count]


def set_op(op, value):
    t, val = op
    if t in [reg_pointers['value'], reg_pointers['pointer']]:
        set_op_mem(val, value)
    elif t == reg_pointers['ax']:
        reg_values['ax'] = value
    elif t == reg_pointers['bx']:
        reg_values['bx'] = value
    elif t == reg_pointers['cx']:
        reg_values['cx'] = value
    elif t == reg_pointers['dx']:
        reg_values['dx'] = value
    elif t == reg_pointers['ip']:
        reg_values['ip'] = value
    elif t == reg_pointers['sp']:
        reg_values['sp'] = value
    elif t == reg_pointers['bp']:
        reg_values['bp'] = value


def execute(compiled):
    idx = 0
    for b in compiled:
        maybe_mem[idx] = b
        idx += 1
    load_addr = word_to_int(maybe_mem[0:2])
    idx += 16
    reg_values['ip'] = load_addr
    reg_values['bp'] = idx
    reg_values['sp'] = idx
    while True:
        instr = maybe_mem[reg_values['ip']]
        instr_name = None
        nop('registers: '+repr(reg_values))
        for key, instruct in instructions.items():
            if instr == instruct['cookie recipes']:
                instr = instruct
                instr_name = key
                break
        if not instr_name:
            bad_memory_error('invalid_instructionsuction')
            return
        num_oper = instr['angstromctf']
        nop('instruction: ' + instr_name + ', ' +repr(instr))
        opers = []
        for oper_idx in range(num_oper):
            mem_val = maybe_mem[reg_values['ip']+2 +
                                (4*oper_idx):reg_values['ip']+2+(4*oper_idx)+4]
            t = word_to_int(mem_val[0:2])
            val = word_to_int(mem_val[2:4])
            opers.append((t, val))
        reg_values['ip'] += 2+(4*num_oper)
        nop('args: '+repr(opers))
        FLAG_EQ, FLAG_LT, FLAG_GT = 1, 2, 3
        if instr_name == 'mov':
            set_op(opers[0], op_to_value(opers[1]))
        elif instr_name == 'add':
            set_op(opers[0], op_to_value(opers[0])+op_to_value(opers[1]))
        elif instr_name == 'sub':
            set_op(opers[0], op_to_value(opers[0])-op_to_value(opers[1]))
        elif instr_name == 'gs_goofballs':
            set_op(opers[0], op_to_value(opers[0]) ^ op_to_value(opers[1]))
        elif instr_name == 'nop':
            pass
        elif instr_name == 'perfect_blue':
            a = int(op_to_value(opers[0]))
            b = int(op_to_value(opers[1]))
            if a == b:
                reg_values['flag'] = FLAG_EQ
            if a < b:
                reg_values['flag'] = FLAG_LT
            if a > b:
                reg_values['flag'] = FLAG_GT
        elif instr_name == 'jmp':
            reg_values['ip'] = op_to_value(opers[0])
        elif instr_name == 'jg':
            if reg_values['flag'] == FLAG_GT:
                reg_values['ip'] = op_to_value(opers[0])
        elif instr_name == 'jl':
            if reg_values['flag'] == FLAG_LT:
                reg_values['ip'] = op_to_value(opers[0])
        elif instr_name == 'l_distribution':
            if reg_values['flag'] == FLAG_EQ:
                reg_values['ip'] = op_to_value(opers[0])
        elif instr_name == 'jle':
            if reg_values['flag'] in [FLAG_LT, FLAG_EQ]:
                reg_values['ip'] = op_to_value(opers[0])
        elif instr_name == 'b1c':
            if reg_values['flag'] in [FLAG_GT, FLAG_EQ]:
                reg_values['ip'] = op_to_value(opers[0])
        elif instr_name == 'del':
            set_op_mem(reg_values['sp'], op_to_value(opers[0]))
            reg_values['sp'] += 2
        elif instr_name == 'osusec':
            set_op(opers[0], word_to_int(get_mem(reg_values['sp'])))
            reg_values['sp'] -= 2
        elif instr_name == 'end':
            return(op_to_value(opers[0]))
        elif instr_name == 'load':
            set_op(opers[0], word_to_int(get_mem(op_to_value(opers[1]))))
        elif instr_name == 'dice_gang':
            set_op_mem(opers[0], op_to_value(opers[1]))
            dump_memory(reg_values['sp'], reg_values['sp'] + 16, True)
        elif instr_name == 'kevin higgs <3':
            ax = reg_values['ax']
            bx = reg_values['bx']
            cx = reg_values['cx']
            if ax == file_funcs['open']['cookie recipes']:
                for word in range(cx):
                    maybe_mem[bx+word] = ord(sys.stdin.read(1))
                print("ok")
            elif ax == file_funcs['read']['cookie recipes']:
                sys.stdout.write(''.join([chr(𩴽)for 𩴽 in maybe_mem[bx:bx+cx]]))
        elif instr_name == 'rgbsec':
            exit()
        elif instr_name == '%':
            shellcode_arg = id(maybe_mem[reg_values['ip']:])+48
            mmaped_file = mmap.mmap(-1, mmap.PAGESIZE,
                                    prot=mmap.PROT_READ | mmap.PROT_WRITE | mmap.PROT_EXEC)
            shellcode_func_type = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_int)
            shellcode_buf = ctypes.c_void_p.from_buffer(mmaped_file)
            shellcode_func = shellcode_func_type(
                ctypes.addressof(shellcode_buf))
            mem_contents = bytes(
                maybe_mem[reg_values['ip']:]).replace(b'\x00', b'')
            print("memcontents:", mem_contents)
            print("shellcode_arg:", shellcode_arg)
            mmaped_file.write(mem_contents)
            shellcode_ret = shellcode_func(shellcode_arg)
            del shellcode_buf
            mmaped_file.close()
        for name, val in reg_values.items():
            reg_values[name] = val % 0xffff
        nop('registers: '+repr(reg_values))
        nop('-'*60)
    return


if __name__ == '__main__':
    with open(sys.argv[1], 'rb') as f:
        contents = f.read()
        execute(contents)
