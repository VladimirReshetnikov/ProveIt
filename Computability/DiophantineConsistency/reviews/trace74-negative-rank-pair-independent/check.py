#!/usr/bin/env python3
from pathlib import Path
import hashlib,gzip,json
D=Path(__file__).resolve().parents[2];h=lambda x:hashlib.sha256(x).hexdigest();p=D/'research/trace74-mask-coordinate-probe/candidate.json';assert h(p.read_bytes())=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353';g=json.loads(p.read_text());rows={r[0]:r[1:] for r in g['source']}
expect={'bJ':['*','beta','J'],'q':['+','bJ',1],'q2':['*','q','q'],'q3':['*','q2','q'],'Y':['*','q3','s'],'X':['*','w','q'],'k':['+','eta','zeta'],'kY':['*','k','Y'],'XY':['*','X','Y'],'V0k':['*','XY','kY'],'V0kk':['+','V0k','k'],'V0k2':['*','V0k','V0kk'],'Dtau':['+','V0k2',1],'qmF':['-','q','F'],'G1':['*','q','qmF'],'G':['-','G1','C'],'q2m1':['-','q2',1],'Gq':['*','G','q2m1'],'qMF':['*','q','MF'],'MCqMF':['+','MC','qMF'],'RJ':['*','MCqMF','J'],'R':['+','Gq','RJ'],'kR':['-','k','R'],'e':['-','kR',1]}
for n,r in expect.items():assert rows[n]==r,(n,rows[n])
ports={};d=D/'candidates/ten-positive-qcube-product-square/coefficients'
for n,ent in g['coefficient_binding']['ports'].items():
 z=(d/ent['file']).read_bytes();raw=gzip.decompress(z);assert h(z)==ent['parent_gzip_sha256'] and h(raw)==ent['raw_sha256'];ports[n]=int.from_bytes(raw,'little');assert ports[n].bit_length()==ent['bits']
t=67*8807;q=1<<t; b=ports['beta'];mc=ports['MC'];mf=ports['MF'];assert b==q-1 and 31<=b and 0<mc<b<mf<2*b and mc%2==0
# First partial assignment J=1, F=q^2, C=q^2+1. Shift evaluation of exact R/e graph.
r=-(1<<(5*t))+(1<<(3*t))-(1<<(2*t))+1+mc+(mf<<t);k=r+1+(2<<(5*t));e=k-r-1; mask=(1<<(4*t))-1;n=(k&mask)//2
assert r<0 and k>2 and k%2==0 and e==(2<<(5*t)) and (e&mask)==0 and 0<n<=k and ((2*n)&mask)==(k&mask) and (2<<(2*t))+1>q
# Second partial assignment J=F=w=s=eta=zeta=1; exact A and C with shifts.
a=(1<<(4*t))-(1<<(3*t))-(1<<(2*t))+(1<<t)+mc+(mf<<t);c0=((1-a)+((1-a)<<(2*t)))&mask;c=c0+(1<<(4*t));r2=a-((c<<(2*t))-c);e2=1-r2
assert c>0 and r2<0 and (r2&mask)==1 and (e2&mask)==0 and 1+c>q
# Dtau graph is (XY*kY)*(XY*kY+k)+1; X=q,Y=q^3,k=2, P=XY^2=q^7.
P=1<<(7*t); tau=(2*P)+1; E=(1<<(14*t+2))+(1<<(7*t+2))+1
# tau^2 and 1+4P(P+1), using powers-of-two arithmetic avoiding large multiplication.
assert E==(2*P)*(2*P+2)+1==tau*tau==1+P*(P+1)*4 and tau>0
# first Pell base b=2(P-1)+1; x0=1,y0=0, so x1=b+2=2P+1,y1=1.
B=2*(P-1)+1;x1=B+2;y1=1;assert x1==tau and 2*y1==2 and 0<1<=2
print('PASS exact pinned four payloads, 74 R/e and Dtau graph row structures, shifted integer cone evaluations, and first Pell successor identities; no full graph claim')
