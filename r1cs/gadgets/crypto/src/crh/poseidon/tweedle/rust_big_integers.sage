def rust_big_int(field_name, bigint, bi_len, mont_const):
    x = hex(bigint*mont_const)
    x = x.replace('0x','',1)
    n = len(x)
    x = (bi_len*64 - n)*'0' + x
    st = "\nfield_new!(\n\t" + field_name + ",\n\tBigInteger(["
    for _ in range(0,bi_len):
        st += "\n\t\t0x" + x[-16:] + ","
        x = x[:-16]
    st += "\n\t])\n),\n"
    return st

def rust_big_int_ls(field_name, bigint_ls, bi_len, mont_const):
    initial_st = "\n&["
    central_st = ''
    for bigint in bigint_ls:
        central_st += rust_big_int(field_name, bigint, bi_len, mont_const)
    central_st = central_st.replace('\n','\n\t')
    final_st =  "\n],"
    return initial_st + central_st + final_st

def rust_big_int_ls_ls(field_name, bigint_ls_ls, bi_len, mont_const):
    initial_st = "\n&["
    central_st = ''
    for bigint_ls in bigint_ls_ls:
        central_st += rust_big_int_ls(field_name, bigint_ls, bi_len, mont_const)
    central_st = central_st.replace('\n','\n\t')
    final_st =  "\n];"
    return initial_st + central_st + final_st

