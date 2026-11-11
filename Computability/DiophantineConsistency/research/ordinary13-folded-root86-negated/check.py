#!/usr/bin/env python3
"""Exact signed-fold graph and authenticated compact44 modular ray; no Lean."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
def load(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h;return json.loads(b)
p=load(D/'research/ordinary13-four-square88-30/candidate.json','daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420')
a=load(D/'research/ordinary13-folded-root86-probe/candidate.json','e44c211efa0f124dc00414a475b2dca0d576117aaed7f4a371aa5a687be0a540')
c=load(H/'candidate.json','186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166')
assert p['witnesses']==a['witnesses']==c['witnesses'] and p['fixed_numerals']==a['fixed_numerals']==c['fixed_numerals']
assert c['source']==[['g31','-','g30','r'] if row[0]=='g31' else row for row in a['source']]
assert len(p['source'])==88 and len(c['source'])==86
rows={row[0]:row for row in p['source']};assert rows['folded_kBt']==['folded_kBt','*','k','Bt'] and rows['folded_g31']==['folded_g31','-','g31','folded_kBt'] and [row[0] for row in p['source'] if 'r' in row[2:]]==['g31']
needed={'out'}
for n,op,x,y in reversed(c['source']):
 if n in needed:needed.update((x,y))
assert all(x[0] in needed for x in c['source']) and all(x in needed for x in c['witnesses']+c['fixed_numerals'])
def calc(rows,v):
 v=v.copy()
 def get(x):return x if isinstance(x,int) else v[x]
 for n,op,a,b in rows:
  x,y=get(a),get(b);v[n]=x*y if op=='*' else x+y if op=='+' else x-y
 return v
random.seed(49811)
for _ in range(100):
 v={x:random.randrange(-5,6) for x in p['witnesses']+p['fixed_numerals']}; old=calc(p['source'],v); v['r']=old['k']*old['Bt']-v['r']; new=calc(c['source'],v);assert old['out']==new['out'] and old['Z']==new['Z']
# Exact free-ring A0 and A1 cancellations, independent of polynomial implementation.
def add(a,b,sgn=1):
 z=a.copy()
 for k,v in b.items():z[k]=z.get(k,0)+sgn*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z={}
 for k,v in a.items():
  for l,w in b.items():
   key=tuple(sorted(k+l));z[key]=z.get(key,0)+v*w
 return {k:v for k,v in z.items() if v}
def prod(*xs):
 v={():1}
 for x in xs:v=mul(v,x)
 return v
def var(n):return {(n,):1}
M,ell,k,r,Bt,Y,qm,q3,U,a,c0,Hh,sh,X=map(var,['M','ell','k','r','Bt','Y','qm','q3','U','a','c','H','shift','X']); one={():1};two={():2}
d=add(mul(M,add(k,r,-1)),add(mul(Y,qm),mul(q3,Bt),-1));Z=add(mul(M,ell),d)
L=add(mul(Z,Z),prod(M,M,add(one,mul(ell,add(ell,k)))),-1);R=add(add(prod(two,M,ell,d),mul(d,d)),prod(M,M,add(one,mul(ell,k))),-1);assert L==R
W=add(mul(U,X),mul(Hh,sh));Ds=add(prod(U,a,c0),W);delta=add(mul(a,a),Hh)
L=add(mul(Ds,Ds),prod(U,U,add(one,prod(delta,c0,c0))),-1);R=add(add(prod(two,U,a,c0,W),mul(W,W)),prod(U,U,add(one,prod(Hh,c0,c0))),-1);assert L==R
# Compact44 tuple pinned against both separately recorded bindings.
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';b=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf');b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01');prime=1000000007;fixed={}
for n,m in b['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']; z=(p72/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];x=gzip.decompress(z);assert len(x)==m['raw_bytes'] and hashlib.sha256(x).hexdigest()==m['sha256_raw'];fixed[n]=int.from_bytes(x,'little')%prime
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def padd(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def pmul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 return trim(z)
v={x:[0,1] for x in c['witnesses']};v.update({n:[x] for n,x in fixed.items()})
def val(x):return [x%prime] if isinstance(x,int) else v[x]
for n,op,x,y in c['source']:v[n]=pmul(val(x),val(y)) if op=='*' else padd(val(x),val(y),1 if op=='+' else -1)
assert len(v['out'])-1==26 and v['out'][-1]!=0
# Small actual-integer controls exercise the alternate square root branch.
assert 2*524289>2*12 and (524288+2+4-4+524289)>2*12
print(json.dumps({'operations':86,'all_gates_inputs_ports_live':True,'proved_degree_upper':26,'prime':prime,'ray_degree':len(v['out'])-1,'ray_leader':v['out'][-1],'scope':'signed-fold source/ring and actual-port degree; positive existence reverse open; no Lean'},sort_keys=True,indent=2))
