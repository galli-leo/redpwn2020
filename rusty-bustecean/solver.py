import z3
from Crypto.Util.number import long_to_bytes

flag = []
for i in range(6 + 8):
    flag.append(z3.BitVec(f'flag_{i}', 64))

def solve(vars = []):
    s = z3.Solver()

    for c in flag:
        # s.add(c >= ord(' '), c <= ord('~'))
        s.add(z3.Or(
            # z3.And(c >= ord('0'), c <= ord('9')),
            z3.And(c >= ord('a'), c <= ord('f')),
            # z3.And(c >= ord('A'), c <= ord('F')),
            c == ord('_'),
            # c == ord(' '),
            # c == ord('.'),
            # c == ord('\'')
        ))
    # s.add(flag[-1] == ord('e'))
    # s.add(flag[-2] == ord('f'))
    # s.add(flag[-3] == ord('f'))
    # s.add(flag[-4] == ord('i'))
    # s.add(flag[-5] == ord('d'))
    def rip(num):
        return int(num / 16)

    def rbx():
        return ((((0x561245 * rip(0x0510)) << 8) | 8) ^ rip(0x0540)) * 0x233

    rcx_orig = (flag[0] << 40) | (flag[1] << 32) | (flag[2] << 24) | (flag[3] << 16) | (flag[4] << 8) | flag[5]
    tmp = (rcx_orig - rbx()) ^ rcx_orig
    s.add(tmp == 0x441d8f8a7954)

    rest = flag[6:]
    inp2 = z3.BitVecVal(0, 64)
    for c in flag:
        inp2 = (inp2 << 8) | c

    tmp2 = inp2 ^ ((tmp + rcx_orig) * 0x3544)
    s.add(tmp2 == 0x4b8142f4f4289b45)

    constraints = []
    for var in vars:
        constr = []
        for idx, c in enumerate(flag):
            bad_char = ord(var[idx])
            constr.append(bad_char != c)
        constraints.append(z3.And(*constr))
    if len(constraints) > 0:
        s.add(z3.Or(*constraints))

    print(s.check())
    print(s.model())
    bs = [s.model().eval(c).as_long() for c in flag]
    print(bs)
    print("".join([chr(c) for c in bs]))