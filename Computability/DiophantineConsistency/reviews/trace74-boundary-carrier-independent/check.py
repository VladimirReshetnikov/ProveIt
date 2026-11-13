#!/usr/bin/env python3
"""Independently check carrier identity and seed residue, without Lean."""
from pathlib import Path
from hashlib import sha256
import json,math
D=Path(__file__).resolve().parents[2];G=D/'research/trace74-mask-coordinate-probe/candidate.json';raw=G.read_bytes();assert sha256(raw).hexdigest()=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353';g=json.loads(raw);rows={r[0]:r[1:] for r in g['source']}
need={'bJ':['*','beta','J'],'q':['+','bJ',1],'q2':['*','q','q'],'q3':['*','q2','q'],'Y':['*','q3','s'],'X':['*','w','q'],'k':['+','eta','zeta'],'kY':['*','k','Y'],'c':['+','kY','eta'],'XY':['*','X','Y'],'Am1':['+','XY','Y'],'4Am1':['*',4,'Am1'],'Hp':['-','4Am1',1],'threec':['*',3,'c'],'twoX':['*',2,'X'],'gap':['-','threec','twoX'],'Kpos0':['*','X','gap'],'Kpos':['+','Kpos0',2], 'P1mu2':['*','bJ','XY'],'LBt':['*','V2','Bt'],'V2':['*','V','V'],'center':['-','n','LBt'],'Hn':['*','Hp','center'],'lin':['+','Hn','Kpos'],'Zpart1':['*','P1mu2','lin'],'mu2inner':['*','XY','Bt'],'P1e':['*','bJ','e'],'brk':['+','mu2inner','P1e'],'Zpart2':['*','Hp','brk'],'Znum':['-','Zpart1','Zpart2'],'Mtot':['*','P1mu2','Hp']}
for k,v in need.items():assert rows[k]==v,(k,rows[k],v)
beta,J,w,s,eta,zeta=1,1,7,1,1187,5985
h=beta*J;q=h+1;X=w*q;Y=q**3*s;c=(eta+zeta)*Y+eta;assert (h,X,Y,c)==(1,14,8,58563)
D0=X*Y;H=4*(D0+Y)-1;K=X*(3*c-2*X)+2;M=h*D0*H
assert (D0,H,K,M)==(112,479,2459256,53648) and K%H==70 and (h*D0*K)%H==176 and math.gcd(D0,H)==1
# The checked source rows yield Z=hD*(H*(n-V²B)+K)-H*(DB+he).
# H divides all terms except hD*K, for all integers B,e,n,V. H|M.
assert M%H==0 and (h*D0*K)%H!=0
print('PASS candidate row identity, D=112 H=479 K=2459256 M=53648, universal Z mod H=176: M cannot divide Z at this seed')
print('No assertion that any trace74 zero implies M|Z at old alpha=0; no Lean or fixed-port zero claim')
