#!/usr/bin/env python3
"""Standard-library certificate for the general radial Delta Ricci formula.

Variables r,x,a,d,v,w stand for r,x,a,Delta(r),Delta'(r),Delta''(r).
Two-jet differentiation is sufficient: metric -> connection -> curvature.
No third derivative of Delta occurs. This script reuses the finite arithmetic
engine and supplies the derivation dr=1, dd=v, dv=w, dx=da=dw=0.
"""
import json
import time
from pathlib import Path
import verify_stdlib as k

k.N = 6
k.ZERO_EXP = (0,)*6
pr,px,pa,pd,pv,pw = [k.variable(i) for i in range(6)]
pS = k.padd(k.pmul(pr,pr),k.pmul(k.pmul(pa,pa),k.pmul(px,px)))
ps = k.padd({k.ZERO_EXP:1},k.pscale(k.pmul(px,px),-1))
k.FACTORS = [{k.ZERO_EXP:2},pS,pd,ps]
k.POWER_CACHE.clear()
def jet_deriv(p,i):
    if i==1:
        return k.padd(k.padd(k.pder(p,0),k.pmul(k.pder(p,3),pv)),k.pmul(k.pder(p,4),pw))
    if i==2: return k.pder(p,1)
    return {}
k.deriv_poly = jet_deriv

r,x,a,d,v,w = [k.Rat(p) for p in (pr,px,pa,pd,pv,pw)]
S,s = k.Rat(pS),k.Rat(ps)
iS,id_,is_ = k.Rat(1,(0,1,0,0)),k.Rat(1,(0,0,1,0)),k.Rat(1,(0,0,0,1))
half = k.Rat(1,(1,0,0,0))
B = r*r+a*a
g,gi = k.matrix(),k.matrix()
g[0][0] = (-d+a*a*s)*iS
g[0][3] = g[3][0] = a*s*(d-B)*iS
g[1][1] = S*id_
g[2][2] = S*is_
g[3][3] = s*(B*B-a*a*d*s)*iS
gi[0][0] = -(B*B-a*a*d*s)*iS*id_
gi[0][3] = gi[3][0] = a*(d-B)*iS*id_
gi[1][1] = d*iS
gi[2][2] = s*iS
gi[3][3] = (d-a*a*s)*iS*id_*is_
k.check('offshell_inverse',(sum(g[i][h]*gi[h][j] for h in range(4))-int(i==j) for i in range(4) for j in range(4)))
dg=[[[g[i][j].diff(h) for j in range(4)] for i in range(4)] for h in range(4)]
Gamma=[[[k.Rat(0) for _ in range(4)] for _ in range(4)] for _ in range(4)]
for i in range(4):
    for j in range(4):
        for h in range(j,4):
            Gamma[i][j][h]=Gamma[i][h][j]=half*sum(gi[i][l]*(dg[j][l][h]+dg[h][l][j]-dg[l][j][h]) for l in range(4))
trace=[sum(Gamma[h][i][h] for h in range(4)) for i in range(4)]
k.check('offshell_trace',(trace[i]-S.diff(i)*iS for i in range(4)))
Ric=k.matrix()
for i in range(4):
    for j in range(4):
        Ric[i][j]=sum(Gamma[h][i][j].diff(h)+Gamma[h][i][j]*trace[h] for h in range(4))-trace[i].diff(j)-sum(Gamma[h][i][l]*Gamma[l][j][h] for h in range(4) for l in range(4))
    k.announce(f'Off-shell Ricci row {i} computed')
V=(r*r-a*a+d-r*v)*iS**2
U=V+half*(w-2)*iS
C=[[k.Rat(1),k.Rat(0),k.Rat(0),-a*s],[k.Rat(0),k.Rat(1),k.Rat(0),k.Rat(0)],[k.Rat(0),k.Rat(0),k.Rat(1),k.Rat(0)],[-a,k.Rat(0),k.Rat(0),B]]
RC=k.matrix()
for i,z in enumerate((U*d*iS,-U*S*id_,V*S*is_,V*s*iS)): RC[i][i]=z
expected=k.mmul(k.mmul(k.transpose(C),RC),C)
k.check('offshell_ricci',(Ric[i][j]-expected[i][j] for i in range(4) for j in range(4)))
k.check('offshell_scalar_curvature',[sum(gi[i][j]*Ric[i][j] for i in range(4) for j in range(4))+(w-2)*iS])
out={'status':'PASS','variables':['r','x','a','d','v','w'],
     'interpretation':'d=Delta(r), v=Delta prime(r), w=Delta double prime(r)',
     'formula':'V=(r^2-a^2+d-r*v)/S^2; U=V+(w-2)/(2*S); Ric coframe diagonal=(U*d/S,-U*S/d,V*S/s,V*s/S)',
     'checks':k.CHECKS,'arithmetic_counters':k.COUNTS,
     'seconds':round(time.monotonic()-k.START,3)}
dest=Path(__file__).resolve().parents[1]/'certificates'/'offshell_results.json'
dest.write_text(json.dumps(out,indent=2)+'\n')
k.announce(f'PASS: wrote {dest.name}')
