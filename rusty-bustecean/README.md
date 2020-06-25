# rusty-bustacean



1. Find rust main with static analysis
2. Find actual main function by dynamic analysis and guessing (its at + 0x1650)
3. Fixup all the switch statements with handler.py so that you can get actual decompiled output
4. Realize it's a shitty custom vm implementation
5. (optional) cry
6. dump asm in debugger
7. convert to readable assembly (disas.py)
8. reverse asm by hand (output_annotated.asm)
9. solve part of it with z3
10. ~~guess the part z3 should be solving, because you don't have enough constraints~~ actually, you have enough constraints since apparently rust cannot overflow primitive types, but I only found that out afterwards.
