#!/usr/bin/env python3
"""Exact Riemann/Kretschmann certificate using only the standard library.

Curvature convention:
R^a_bcd = d_c Gamma^a_db - d_d Gamma^a_cb
          + Gamma^a_ce Gamma^e_db - Gamma^a_de Gamma^e_cb.
Ric_bd = R^a_bad.  Antisymmetric pair bases reduce the final contraction
to 6 by 6 matrix arithmetic, with the explicit multiplicity factor four.
"""
import json
import time
from pathlib import Path
import verify_stdlib as k

r,x,a,m,q = [k.Rat(p) for p in (k.P_R,k.P_X,k.P_A,k.P_M,k.P_Q)]
S,D,s = k.Rat(k.P_S),k.Rat(k.P_D),k.Rat(k.P_s)
iS,iD,is_ = k.Rat(1,(0,1,0,0)),k.Rat(1,(0,0,1,0)),k.Rat(1,(0,0,0,1))
half = k.Rat(1,(1,0,0,0))
B = r*r+a*a
g,gi = k.matrix(),k.matrix()
g[0][0] = (-D+a*a*s)*iS
g[0][3] = g[3][0] = a*s*(D-B)*iS
g[1][1] = S*iD
g[2][2] = S*is_
g[3][3] = s*(B*B-a*a*D*s)*iS
gi[0][0] = -(B*B-a*a*D*s)*iS*iD
gi[0][3] = gi[3][0] = a*(D-B)*iS*iD
gi[1][1] = D*iS
gi[2][2] = s*iS
gi[3][3] = (D-a*a*s)*iS*iD*is_
dg = [[[g[i][j].diff(h) for j in range(4)] for i in range(4)] for h in range(4)]
Gamma = [[[k.Rat(0) for _ in range(4)] for _ in range(4)] for _ in range(4)]
for i in range(4):
    for j in range(4):
        for h in range(j,4):
            Gamma[i][j][h] = Gamma[i][h][j] = half*sum(gi[i][l]*(dg[j][l][h]+dg[h][l][j]-dg[l][j][h]) for l in range(4))
k.announce('Christoffel symbols computed')
RU = {}
for c in range(4):
    for d in range(c+1,4):
        for aa in range(4):
            for b in range(4):
                RU[aa,b,c,d] = Gamma[aa][d][b].diff(c)-Gamma[aa][c][b].diff(d)+sum(Gamma[aa][c][e]*Gamma[e][d][b]-Gamma[aa][d][e]*Gamma[e][c][b] for e in range(4))
        k.announce(f'Riemann last pair {c}{d} computed')

def riemann_up(aa,b,c,d):
    if c==d: return k.Rat(0)
    if c<d: return RU[aa,b,c,d]
    return -RU[aa,b,d,c]

RL = {}
for aa in range(4):
    for b in range(4):
        for c in range(4):
            for d in range(c+1,4):
                RL[aa,b,c,d] = sum(g[aa][e]*RU[e,b,c,d] for e in range(4))

def riemann(aa,b,c,d):
    if c==d: return k.Rat(0)
    if c<d: return RL[aa,b,c,d]
    return -RL[aa,b,d,c]

k.check('riemann_first_pair_antisymmetry',(riemann(aa,b,c,d)+riemann(b,aa,c,d) for aa in range(4) for b in range(aa,4) for c in range(4) for d in range(c+1,4)))
pairs = [(aa,b) for aa in range(4) for b in range(aa+1,4)]
L = [[riemann(aa,b,c,d) for c,d in pairs] for aa,b in pairs]
k.check('riemann_pair_symmetry',(L[i][j]-L[j][i] for i in range(6) for j in range(i+1,6)))
k.check('riemann_algebraic_bianchi',(riemann(aa,b,c,d)+riemann(aa,c,d,b)+riemann(aa,d,b,c) for aa in range(4) for b in range(4) for c in range(b+1,4) for d in range(c+1,4)))
Ric = [[sum(riemann_up(aa,b,aa,d) for aa in range(4)) for d in range(4)] for b in range(4)]
C = [[k.Rat(1),k.Rat(0),k.Rat(0),-a*s],[k.Rat(0),k.Rat(1),k.Rat(0),k.Rat(0)],[k.Rat(0),k.Rat(0),k.Rat(1),k.Rat(0)],[-a,k.Rat(0),k.Rat(0),B]]
RC = k.matrix()
for i,z in enumerate((q*q*D*iS**3,-q*q*iS*iD,q*q*iS*is_,q*q*s*iS**3)): RC[i][i] = z
expected_Ric = k.mmul(k.mmul(k.transpose(C),RC),C)
k.check('riemann_ricci_contraction',(Ric[i][j]-expected_Ric[i][j] for i in range(4) for j in range(4)))
RicU = k.mmul(k.mmul(gi,Ric),gi)
Ric2 = sum(Ric[i][j]*RicU[i][j] for i in range(4) for j in range(4))
k.check('ricci_squared',[Ric2-4*q**4*iS**4])

# For an antisymmetric pair A=(a,b), B=(c,d), define the inverse
# bivector metric G_AB = g^ac*g^bd - g^ad*g^bc.  Raising both pairs
# of the stored lower curvature matrix gives G*L*G, and summing all
# ordered tensor indices introduces one factor two for each pair.
G = [[gi[aa][c]*gi[b][d]-gi[aa][d]*gi[b][c] for c,d in pairs] for aa,b in pairs]
def mul6(A,B): return [[sum(A[i][h]*B[h][j] for h in range(6)) for j in range(6)] for i in range(6)]
LU = mul6(mul6(G,L),G)
k.announce('Both Riemann index pairs raised')
K = 4*sum(L[i][j]*LU[i][j] for i in range(6) for j in range(6))
k.announce('Kretschmann scalar contracted')
z = a*a*x*x
expected_K = 8*iS**6*(6*m*m*(r**6-15*r**4*z+15*r*r*z*z-z**3)-12*m*q*q*r*(r**4-10*r*r*z+5*z*z)+q**4*(7*r**4-34*r*r*z+7*z*z))
k.check('kretschmann',[K-expected_K])

def specialize(poly, zeros):
    """Set selected polynomial variables to zero, retaining all others."""
    return {e:c for e,c in poly.items() if all(e[j]==0 for j in zeros)}

# With m=q=0 every lower Riemann numerator vanishes.  This is stronger
# than K=0, which alone would not establish Lorentzian flatness.
k.check('flat_when_m_q_zero',(k.Rat(specialize(v.p,(3,4)),v.d) for v in RL.values()))
# The equatorial numerator of K equals 8*r^4*[6*(m*r-q^2)^2+q^4].
equatorial_numerator = specialize(expected_K.p,(1,))
equatorial_expected = 8*r**4*(6*(m*r-q*q)**2+q**4)
k.check('equatorial_kretschmann_numerator',[k.Rat(equatorial_numerator)-equatorial_expected])

out={'status':'PASS','engine':'Python standard library only','checks':k.CHECKS,
     'pair_order':[[aa,b] for aa,b in pairs],
     'ricci_squared':'4*q^4/S^4',
     'kretschmann':'8/S^6 * (6*m^2*(r^6-15*r^4*a^2*x^2+15*r^2*a^4*x^4-a^6*x^6)-12*m*q^2*r*(r^4-10*r^2*a^2*x^2+5*a^4*x^4)+q^4*(7*r^4-34*r^2*a^2*x^2+7*a^4*x^4))',
     'equatorial_kretschmann':'8*(6*(m*r-q^2)^2+q^4)/r^8',
     'arithmetic_counters':k.COUNTS,
     'seconds':round(time.monotonic()-k.START,3)}
dest=Path(__file__).resolve().parents[1]/'certificates'/'curvature_results.json'
dest.write_text(json.dumps(out,indent=2)+'\n')
k.announce(f'PASS: wrote {dest.name}')
