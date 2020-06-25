import idc

goal = 0x408B40

def calc_offset(addr):
    return addr + 87

def direction(dir):
    if dir == 1:
        return -1, 51
    if dir == 2:
        return -1, 1
    if dir == 3:
        return 1, 1
    if dir == 4:
        return 1, 51

def next_node(addr, dir):
    a, b = direction(dir)
    return calc_offset(addr) + 106 * a * b - 87

def neighbours(addr):
    mnem = idc.GetDisasm(addr)
    instr = mnem.split(' ')[0]
    if instr == "xor":
        return []
    ret = []
    for dir in [1, 2, 3, 4]:
        ret.append(next_node(addr, dir))
    return ret

marked = set()

def start_dfs(start):
    global marked
    marked = set()
    run_dfs(start, [])

def run_dfs(current, path):
    global marked
    if current == goal:
        print("Found path to target: ", path)
        print("".join([str(d) for d in path]))
    marked.add(current)
    for idx, v in enumerate(neighbours(current)):
        if v not in marked:
            run_dfs(v, path + [idx+1])
