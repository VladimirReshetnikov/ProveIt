#!/usr/bin/env python3
import hashlib,itertools,json,subprocess,sys
from collections import defaultdict
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];pkg=root/'research/current14-carrier65-main-norm-shear';src=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(src)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(src.read_bytes());rs=g['source'];by={r[0]:r for r in rs};assert len(rs)==65 and g['output']=='polynomial'
for row in (['kY','*','k','Y'],['ell','*','E','kY'],['N1','-','main_square','Dc2'],['R','+','rproduct','mask'],['tau','-','tau_partial','R'],['cTminusR','-','cT','R'],['normalized_S','*','i','Dc2'],['scaled_Ns','-','scaled_f2','normalized_S2'],['product0','*','N0','N1'],['product1','*','product0','Na'],['product3','*','product1','Nt'],['product4','*','product3','scaled_Ns'],['polynomial','-','product4','Delta']):assert by[row[0]]==row
assert sum(x=='R' for r in rs for x in r[2:])==2
# Neither anchor has rank as an upstream dependency.
def closure(name):
 seen=set();stack=[name]
 while stack:
  n=stack.pop()
  if n not in seen:
   seen.add(n)
   if n in by:stack.extend(by[n][2:])
 return seen
assert 'R' not in closure('N1') and 'R' not in closure('Nt')
assert all((x*x-(L*L-1)*y*y)%4!=3 for x,L,y in itertools.product(range(4),repeat=3))
# Construct the H=1 sheared gate graph and independently count live gates.
idx=next(i for i,r in enumerate(rs) if r[0]=='R');new=rs[:idx+1]+[['rank_plus_main','+','R','N1'],['sheared_rank','-','rank_plus_main',1]]+[[r[0],r[1]]+['sheared_rank' if x=='R' else x for x in r[2:]] for r in rs[idx+1:]]
def live(rows):
 d={r[0]:r[2:] for r in rows};seen=set();todo=[g['output']]
 while todo:
  x=todo.pop()
  if x in d and x not in seen:seen.add(x);todo.extend(d[x])
 return len(seen)
assert live(rs)==65 and live(new)==67 and len(new)==67
# Independent descent controls for the positive-pronic negative Pell obstruction.
for m in range(2,100):
 for y in range(1,100):
  D=m*(m+1);z=D*y*y-1;x=__import__('math').isqrt(z);assert x*x!=z
# Prove the stated difference formula in an independent exponent-vector polynomial ring.
n=9;zero=(0,)*n
V=[{tuple(int(i==j) for i in range(n)):1} for j in range(n)];Q,t,N0,Na,S2,Vv,f2,Nt,Z=V;one={zero:1}
def plus(a,b,k=1):
 c=defaultdict(int,a)
 for x,v in b.items():c[x]+=k*v
 return {x:v for x,v in c.items() if v}
def mul(a,b):
 c=defaultdict(int)
 for x,u in a.items():
  for y,v in b.items():c[tuple(i+j for i,j in zip(x,y))]+=u*v
 return {x:v for x,v in c.items() if v}
def prod(*xs):
 z=one
 for x in xs:z=mul(z,x)
 return z
def sc(a,k):return {x:k*v for x,v in a.items() if k*v}
d=plus(Q,one,-1);shiftN0=plus(N0,plus(sc(mul(t,d),-2),mul(d,d)));inner=plus(sc(prod(Vv,f2,d),-2),prod(f2,f2,d,d));shiftNa=plus(Na,mul(S2,inner));left=prod(Q,Nt,Z,plus(mul(shiftN0,shiftNa),mul(N0,Na),-1));right=prod(Q,Nt,Z,d,plus(mul(plus(sc(t,-2),d),shiftNa),prod(N0,S2,plus(sc(mul(Vv,f2),-2),prod(f2,f2,d)))));assert left==right
r=subprocess.run([sys.executable,'-I','-S','-B',str(pkg/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not r.stderr and json.loads(r.stdout)==json.loads((pkg/'result.json').read_text())
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'N1 anchored coordinatewise rank shear, H=1 costs 67 gates; external mathematics, no Lean/PDF theorem or gate reduction'},indent=2))
