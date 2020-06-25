import idaapi
import ida_bytes
import idc
import idautils

class MyHandler(idaapi.action_handler_t):
    def __init__(self):
        idaapi.action_handler_t.__init__(self)
    # Say hello when invoked.
    def activate(self, ctx):
        screen_ea = idaapi.get_screen_ea()
        gen_xrefs = idautils.XrefsTo(screen_ea, 0)
        for xx in gen_xrefs:
            ref_loc = xx.frm
            print("Creating switch idiom at ea: ", hex(ref_loc))
            jmp_loc = ref_loc + 14
            print("Jump instruction should be at: ", hex(jmp_loc))
            ins = idautils.DecodeInstruction(jmp_loc)
            name = ins.get_canon_mnem()
            if name != "jmp":
                print("Warning found instruction ", name)
                continue
            if ins.Op1.type != idaapi.o_reg:
                print("Warning found non reg as operand")
                continue
            reg_num = ins.Op1.reg
            reg_name = idaapi.get_reg_name(reg_num, 8)
            print("Jump register is named ", reg_name)
            s = idaapi.switch_info_t()
            s.flags |= idaapi.SWI_SIGNED | idaapi.SWI_ELBASE
            s.elbase = screen_ea
            s.set_jtable_element_size(4)
            s.ncases = 6
            s.set_expr(reg_num, 7)
            s.jumps = screen_ea
            s.startea = jmp_loc
            idaapi.set_switch_info(jmp_loc, s)
            idaapi.create_switch_table(jmp_loc, s)
        return 1
    def create_table(self):
        screen_ea = idaapi.get_screen_ea()
        print("Creating table at: ", hex(screen_ea))
        ida_bytes.del_items(screen_ea, 0, 4*6)
        ret = ida_bytes.create_data(screen_ea, ida_bytes.FF_DWORD, 4, idaapi.BADNODE)
        print("got return: ", ret)
        idc.MakeArray(screen_ea, 6)
    # This action is always available.
    def update(self, ctx):
        return idaapi.AST_ENABLE_ALWAYS

action_desc = idaapi.action_desc_t(
    'rusty:table',   # The action name. This acts like an ID and must be unique
    'Create Table!',  # The action text.
    MyHandler(),   # The action handler.
    'Ctrl+Shift+E',      # Optional: the action shortcut
    'Create Table!',  # Optional: the action tooltip (available in menus/toolbar)
    199)           # Optional: the action icon (shows when in menus/toolbars)

idaapi.unregister_action('rusty:table')

idaapi.register_action(action_desc)
form = idaapi.get_current_tform()
idaapi.attach_action_to_popup(form, None, "rusty:table", None)
idaapi.attach_action_to_menu(
        'Edit/Other/Manual instruction...', # The relative path of where to add the action
        'rusty:table',                        # The action ID (see above)
        idaapi.SETMENU_APP)