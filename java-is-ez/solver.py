import z3

def calc_sum(inp):
    ret = 0
    for c in inp:
        ret = (ret * 31 + ord(c)) & 0xffffffff
    return ret

static_strings = ["redpwn", "ctf2020"]
static_longs = [8248156489741230770, -5342668067454976247, -889275714, -559038737]

static_nums = [calc_sum(l) for l in static_strings]

flag = []
for i in range(32 + 6): # we know flag is at most 32 chars
    flag.append(z3.BitVec(f'flag_{i}', 8)) # char is 8 bits

begin = "flag{"

s = z3.Solver()

parse_byte = z3.Function('parse_byte', z3.BitVecSort(16), z3.BitVecSort(8))

def hex_nibble(num, large):
    if large:
        return ord(f"{num:X}")
    return ord(f"{num:x}")

for i in range(256):
    upper = (i >> 4)
    lower = i & 0xf
    for ul in [False, True]:
        for ll in [False, True]:
            a = hex_nibble(upper, ul)
            b = hex_nibble(lower, ll)
            inp = z3.BitVecVal((a << 8) | b, 16)
            s.add(parse_byte(inp) == i)

def parse_long(chars):
    res = []
    for i in range(0, 16, 2):
        a = chars[i]
        b = chars[i+1]
        res.append((z3.ZeroExt(8, a) << 8) | z3.ZeroExt(8, b))
    chars = res
    def pl(b):
        return z3.ZeroExt(64 - 8, parse_byte(b))
    return (pl(chars[0]) << 56) | (pl(chars[1]) << 48) | (pl(chars[2]) << 40) | (pl(chars[3]) << 32) | (pl(chars[4]) << 24) | (pl(chars[5]) << 16) | (pl(chars[6]) << 8) | (pl(chars[7]))

print("sanity checking parse_byte function")
print(s.check())
print(s.model().eval(z3.BitVecVal(int('aF', 16), 16)))

for idx, c in enumerate(begin):
    s.add(flag[idx] == ord(c))

s.add(flag[-1] == ord('}'))

for c in flag[5:-1]: # change our domain to allow 0
    s.add(z3.Or(
        z3.And(c >= ord('0'), c <= ord('9')),
        z3.And(c >= ord('a'), c <= ord('f')),
        z3.And(c >= ord('A'), c <= ord('F'))
    ))

target = 1140336659
# res = z3.BitVecVal(0, 32)
# flag_len = len(flag)
# for idx, c in enumerate(flag):
#     res = res + z3.ZeroExt(24, c) * (31**(flag_len - idx - 1))
# print(res)
r3 = z3.BitVecVal(0, 32)
for c in flag:
    r3 = r3 * 31 + z3.ZeroExt(24, c)
s.add(r3 == target)
# s.add(res == target)

act_inp = flag[5:-1]
a, b = act_inp[:16], act_inp[16:]
for idx, num in enumerate([a]):
    r3 = static_nums[idx]
    asdf = (r3 | (r3 << 32))
    stat1 = static_longs[idx]
    stat2 = static_longs[idx + 2]
    res1 = asdf ^ stat1
    r5 = parse_long(num)
    s.add(r5 <= 0x7fffffffffffffff)
    res2 = r5 * stat2
    s.add(res1 == res2)

print(s)
print(s.check())

print("".join([chr(s.model().eval(c).as_long()) for c in flag]))