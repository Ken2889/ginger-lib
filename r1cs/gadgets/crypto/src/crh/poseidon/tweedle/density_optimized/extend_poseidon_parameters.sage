load('dee_parameters.sage')
load('rust_big_integers.sage')

rc = [[F(round_constants[t*i + j]) for j in range(0,t)] for i in range(0,R_P + R_F)]

MDS = zero_matrix(F,t,t)
for i in range(0,t):
    for j in range(0,t):
        MDS[i,j] = F(MDS_matrix[i][j])

a = MDS[1,0]/MDS[0,0]; b = MDS[1,1] - MDS[1,0]*MDS[0,1]/MDS[0,0]; c = MDS[1,2] - MDS[1,0]*MDS[0,2]/MDS[0,0]
d = MDS[2,0]/MDS[0,0]; e = MDS[2,1] - MDS[2,0]*MDS[0,1]/MDS[0,0]; f = MDS[2,2] - MDS[2,0]*MDS[0,2]/MDS[0,0]

bcef = [Matrix([[b,c],[e,f]])^i for i in range(0,5)]
b = [bcef[i][0,0] for i in range(0,5)]; c = [bcef[i][0,1] for i in range(0,5)]; 
e = [bcef[i][1,0] for i in range(0,5)]; f = [bcef[i][1,1] for i in range(0,5)];
ad = [bcef[i]*Matrix([[a],[d]]) for i in range(0,5)]
a = [ad[i][0,0] for i in range(0,5)]; d = [ad[i][1,0] for i in range(0,5)]

LC_yz = Matrix([[b[i]*MDS[0,1] + e[i]*MDS[0,2], c[i]*MDS[0,1] + f[i]*MDS[0,2]] for i in range(0,5)])
LC_x = zero_matrix(F,5,5)
for i in range(1,5):
    for j in range(0,i):
        LC_x[i,j] = MDS[0,1]*a[i-j-1] + MDS[0,2]*d[i-j-1]
LC = LC_yz.augment(LC_x)
LC = [list(LC[i]) for i in range(0,5)]

v = [[Matrix([[rc[i][1]],[rc[i][2]]])] for i in range(0,R_F + R_P - 4)]
for i in range(0,R_F + R_P - 4):
    vnew = copy(v[i][0])
    for j in range(1,5):
        vnew = Matrix([[rc[i+j][1]],[rc[i+j][2]]]) + bcef[1]*vnew
        v[i].append(vnew)

alpha = [[   (Matrix([[MDS[0,1], MDS[0,2]]]) * v[i][j])[0,0]  for j in range(0,5) ] for i in range(0, R_F + R_P - 4)]
beta =  [[   (Matrix([[b[1],c[1]]])*v[i][j-1])[0,0]  for j in range(0,5) ] for i in range(0, R_F + R_P - 4)]
gamma = [[   (Matrix([[e[1],f[1]]])*v[i][j-1])[0,0]  for j in range(0,5) ] for i in range(0, R_F + R_P - 4)]


pos_param ={
    'F': F,
    'R_F': R_F,
    'R_P': R_P,
    'rc': rc,
    'MDS': MDS,
    'a': a, 'b': b, 'c': c, 'd': d, 'e': e, 'f': f,
    'alpha': alpha, 'beta': beta, 'gamma': gamma,
    'LC': LC
}

R = F(2)^256
for x in ['a','b','c','d','e','f']:
    print('const ' + x.upper() + ': ' + '&[TweedleFr] = ' + rust_big_int_ls('TweedleFr', pos_param[x], 4, R) +'\n')
for x in ['alpha','beta','gamma','LC']:
    print('const ' + x.upper() + ': ' + '&[&[TweedleFr]] = ' + rust_big_int_ls_ls('TweedleFr', pos_param[x], 4, R) + '\n')