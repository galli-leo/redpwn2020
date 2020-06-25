from pwn import *
import angr
import claripy
from pwn import *

project = angr.Project("./r1sc")
flag = claripy.BVS("flag", 8*48)
state = project.factory.entry_state(stdin=flag)
avoid = [0x401042, 0x40103B]
find = 0x401050
sm = project.factory.simulation_manager(state)
with log.progress("exploring") as p:
    i = 0
    def stepper(sm):
        global i
        i += 1
        if len(sm.active) > 0 and i % 100 == 0:
            s = sm.active[0]
            rip = s.solver.eval(s.regs.rip)
            p.status("exec at 0x%x", rip)
        #p.status("No more actives!")
    sm.explore(find=find, avoid=avoid, step_func=stepper)
