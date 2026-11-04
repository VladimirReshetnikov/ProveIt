#!/usr/bin/env python3
from pathlib import Path
import gzip,hashlib,json
D=Path(__file__).resolve().parents[2];h=lambda x:hashlib.sha256(x).hexdigest();p=D/'research/trace74-mask-coordinate-probe/candidate.json';assert h(p.read_bytes())=='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353';g=json.loads(p.read_text());rows={r[0]:r[1:] for r in g['source']}
expected={'bJ':['*','beta','J'],'q':['+','bJ',1],'q2':['*','q','q'],'q3':['*','q2','q'],'Y':['*','q3','s'],'X':['*','w','q'],'k':['+','eta','zeta'],'kY':['*','k','Y'],'c':['+','kY','eta'],'XY':['*','X','Y'],'V0k':['*','XY','kY'],'V0kk':['+','V0k','k'],'V0k2':['*','V0k','V0kk'],'Dtau':['+','V0k2',1],'qmF':['-','q','F'],'G1':['*','q','qmF'],'G':['-','G1','C'],'q2m1':['-','q2',1],'Gq':['*','G','q2m1'],'qMF':['*','q','MF'],'MCqMF':['+','MC','qMF'],'RJ':['*','MCqMF','J'],'R':['+','Gq','RJ'],'kR':['-','k','R'],'e':['-','kR',1]}
for n,r in expected.items():assert rows[n]==r,(n,rows[n])
ports={};d=D/'candidates/ten-positive-qcube-product-square/coefficients'
for n,ent in g['coefficient_binding']['ports'].items():
 z=(d/ent['file']).read_bytes();raw=gzip.decompress(z);assert h(z)==ent['parent_gzip_sha256'] and h(raw)==ent['raw_sha256'];ports[n]=int.from_bytes(raw,'little');assert ports[n].bit_length()==ent['bits']
t=67*8807;q=1<<t;b=ports['beta'];mc=ports['MC'];mf=ports['MF'];assert b==q-1 and 31<=b and 0<mc<b<mf<2*b
mask=(1<<(4*t))-1;P=1<<(7*t);k=8*P+4;a=(1<<(4*t))-(1<<(3*t))-(1<<(2*t))+(1<<t)+mc+(mf<<t);c0=((3-a)+((3-a)<<(2*t)))&mask;c=c0+(1<<(4*t));r=a-((c<<(2*t))-c);e=k-r-1
assert k>2 and (k&mask)==4 and r<0 and (r&mask)==3 and (e&mask)==0 and 1+c>q
# Actual q, X, Y, k, Dtau rows reduce to E=1+P*(P+1)*k^2.
# Integer coefficient polynomials in P, computed independently of author's q-polynomial checker.
def add(a,b):
 z=a.copy()
 for i,x in b.items():z[i]=z.get(i,0)+x
 return {i:x for i,x in z.items() if x}
def mul(a,b):
 z={}
 for i,x in a.items():
  for j,y in b.items():z[i+j]=z.get(i+j,0)+x*y
 return {i:x for i,x in z.items() if x}
one={0:1};v={1:1};kp={1:8,0:4};base={1:2,0:1};delta={2:4,1:4}
x1=base;y1=one;x2=add(mul(base,x1),mul(delta,y1));y2=add(x1,mul(base,y1))
assert x2=={2:8,1:8,0:1} and y2=={1:4,0:2} and mul({0:2},y2)==kp
E=add(one,mul(mul(v,add(v,one)),mul(kp,kp)));assert E==mul(x2,x2)
# For the same eta=1 tuple, c=k*q^3+1=8q^10+4q^3+1, and k=8P+4.
cv=(8<<(10*t))+(4<<(3*t))+1;assert cv>(2<<(4*t)) and k==8*P+4
print('PASS all payload hashes, pinned JSON rows, exact n=2 scalar R/e and first-Pell polynomial recurrence plus c size; no full graph or Pell2 claim')
