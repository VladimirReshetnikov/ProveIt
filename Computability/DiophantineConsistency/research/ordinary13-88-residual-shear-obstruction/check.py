#!/usr/bin/env python3
"""Compact44 modular rays and exact main cancellation; no Lean."""
import gzip,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def read(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
p=D/'research/ordinary13-four-square88-30/candidate.json';g=json.loads(read(p,'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'));rows={r[0]:r for r in g['source']}
for n,row in {'U':['U','*','Y','q2'],'a':['a','+','E','Y'],'c':['c','+','eta','kY'],'H':['H','+',3,'g15'],'Dstar':['Dstar','+','g58','g59'],'A1':['A1','-','g61','g65'],'Fam':['Fam','-','Fa',1],'g72':['g72','-','g71','Q']}.items():assert rows[n]==row
# Exact cancellation in a free sparse integer-polynomial ring.
def add(a,b,s=1):
 z=a.copy()
 for m,v in b.items():z[m]=z.get(m,0)+s*v
 return {m:v for m,v in z.items() if v}
def mul(a,b):
 z={}
 for m,v in a.items():
  for n,w in b.items():
   k=tuple(sorted(m+n));z[k]=z.get(k,0)+v*w
 return {m:v for m,v in z.items() if v}
def prod(*xs):
 z={():1}
 for x in xs:z=mul(z,x)
 return z
def var(x):return {(x,):1}
U,a,c,H,shift,X=map(var,['U','a','c','H','shift','X']);one={():1};two={():2};W=add(mul(U,X),mul(H,shift));Dstar=add(prod(U,a,c),W);Delta=add(mul(a,a),H)
assert add(mul(Dstar,Dstar),prod(U,U,add(one,prod(Delta,c,c))),-1)==add(add(prod(two,U,a,c,W),mul(W,W)),prod(U,U,add(one,prod(H,c,c))),-1)
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';b=json.loads(read(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'));b115=json.loads(read(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'));prime=1000000007;fixed={}
for n,m in b['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=read(p72/m['path'],m['sha256_gzip']);data=gzip.decompress(z);assert len(data)==m['raw_bytes'] and hashlib.sha256(data).hexdigest()==m['sha256_raw'];fixed[n]=int.from_bytes(data,'little')%prime
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def addp(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mulp(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 return trim(z)
def ray(special):
 v={n:[0,1] for n in g['witnesses']};v.update({n:[x] for n,x in fixed.items()})
 if special:
  beta=fixed['beta'];v.update({'f':[0],'i':[0],'u':[0],'gamma':[0,(-beta*(beta-1))%prime]})
 def get(x):return [x%prime] if isinstance(x,int) else v[x]
 for n,op,a,b in g['source']:v[n]=mulp(get(a),get(b)) if op=='*' else addp(get(a),get(b),1 if op=='+' else -1)
 return {n:{'degree':len(v[n])-1,'leader':v[n][-1]} for n in ('A0','A1','Fam','g72')}
generic=ray(False); special=ray(True)
assert [generic[n]['degree'] for n in ('A0','A1','Fam','g72')]==[15,13,13,10]
assert special['A0']=={'degree':15,'leader':142738814} and special['A1']['degree']<=12 and special['Fam']['degree']<=12 and special['g72']['degree']<=9
print(json.dumps({'prime':prime,'fixed_residues':fixed,'generic':generic,'annihilating':special,'scope':'bounded low-degree exact residual-shear obstruction only; no Lean or global minimality'},sort_keys=True,indent=2))
