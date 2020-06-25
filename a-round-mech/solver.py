import z3

flag = []
for i in range(22): # we know flag is at most 32 chars
    flag.append(z3.BitVec(f'flag_{i}', 8)) # char is 8 bits

after_xor = []
for c in flag:
    after_xor.append(c ^ 0x12)

final = [after_xor[0]]
for i in range(1, 22):
    prev = final[i-1]
    curr = after_xor[i]
    tmp = z3.ZeroExt(24, (prev >> 1)) + 2*z3.ZeroExt(24, curr)
    f = z3.Extract(7, 0, (tmp >> (tmp >> 7)) - 1)
    # tmp = (prev >> 1) + 2 * curr
    # f = (tmp >> (tmp >> 7)) - 1
    final.append(f)

s = z3.Solver()

target = "te@B}efFk~{^Ixv@}y\\BC4"
for idx, c in enumerate(final):
    t = target[21 - idx]
    s.add(c == ord(t))

print(s.check())
print(s.model())

print("".join([chr(s.model().eval(c).as_long()) for c in flag]))

bs = [s.model().eval(c).as_long() for c in flag]
