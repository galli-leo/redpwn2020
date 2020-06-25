import z3
import itertools
from numpy import int32, int64

def calc_sum(inp):
    ret = int32(0)
    for c in inp:
        cv = int32(ord(c))
        ret = (ret * 31 + cv)
    return int32(ret)

def calc_sum_old(inp):
    ret = 0
    for c in inp:
        ret = (ret * 31 + ord(c)) & 0xffffffff
    return ret

static_strings = ["redpwn", "ctf2020"]
static_longs = [8248156489741230770, -5342668067454976247, -889275714, -559038737]

static_nums = [calc_sum(l) for l in static_strings]

def hex_nibble(num, large):
    if large:
        return ord(f"{num:X}")
    return ord(f"{num:x}")

def possible(num):
    chars = []
    #print(f"possible for num: {num:x}")
    for b in range(16):
        shift_down = (15 - b) * 4
        n = (num >> shift_down) & 0xf
        #print(f"doing nibble {b}: {n:x}")
        if n < 10:
            chars.append([f"{n}"])
        else:
            chars.append([f"{n:x}", f"{n:X}"])
    return itertools.product(*chars)

def run_calc(num, idx):
    r3 = int64(static_nums[idx])
    asdf = (r3 | (r3 << 32))
    stat1 = int64(static_longs[idx])
    stat2 = int64(static_longs[idx + 2])
    res1 = asdf ^ stat1
    r5 = int64(num)
    # s.add(r5 <= 0x7fffffffffffffff)
    res2 = r5 * stat2
    return res1, res2

def get_solution(bad_num):
    s = z3.Solver()

    a, b = z3.BitVec('a', 64), z3.BitVec('b', 64)
    for idx, num in enumerate([a, b]):
        r3 = z3.BitVecVal(int(static_nums[idx]), 32)
        r3 = z3.SignExt(32, r3)
        asdf = (r3 | (r3 << 32))
        stat1 = z3.BitVecVal(static_longs[idx], 64)
        stat2 = z3.BitVecVal(static_longs[idx + 2], 64)
        res1 = asdf ^ stat1
        r5 = num
        # s.add(r5 <= 0x7fffffffffffffff)
        res2 = r5 * stat2
        s.add(res1 == res2)

    for ba, bb in bad_num:
        s.add(z3.Or(a != ba, b != bb))
    assert s.check() == z3.sat
    ea = s.model().eval(a).as_long()
    eb = s.model().eval(b).as_long()
    return ea, eb

ea = 0
eb = 0
bad_nums = []
for i in range(10):
    ea, eb = get_solution(bad_nums)
    target = 1140336659
    print(f"found model: {ea:X} {eb:X}")
    a_poss = list(possible(ea))
    b_poss = list(possible(eb))
    print(f"possible combinations", len(a_poss), len(b_poss))
    for a_comb in a_poss:
        for b_comb in b_poss:
            flag = f"flag{{{''.join(a_comb)}{''.join(b_comb)}}}"
            # print("testing flag: ", flag)
            if calc_sum(flag) == target:
                print(f"we got flag!: {flag}")
                break
    bad_nums.append((ea, eb))
        # flag = f"flag{{{ea:X}{eb:X}}}"
        # if len(flag) == 38:
        #     res = calc_sum(flag)
        #     if res == target:
        #         break
        # else:
        #     print("bad length!")

print("Model was actually good!")