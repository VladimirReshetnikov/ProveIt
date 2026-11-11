#!/usr/bin/env python3
"""Conditional 86-gate root absorption, exact cuts and compact-port ray."""
import gzip,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
p=D/'research/ordinary13-four-square88-30/candidate.json';raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()=='daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420'
g=json.loads(raw);rows=g['source'];src={r[0]:r for r in rows}
assert src['folded_kBt']==['folded_kBt','*','k','Bt'] and src['folded_g31']==['folded_g31','-','g31','folded_kBt'] and src['g32']==['g32','*','M','folded_g31']
assert [r[0] for r in rows if 'r' in r[2:]]==['g31']
new=[]
for row in rows:
 if row[0] in ('folded_kBt','folded_g31'):continue
 if row[0]=='g32':row=['g32','*','M','g31']
 new.append(row)
assert len(new)==86
cb=(H/'candidate.json').read_bytes();assert hashlib.sha256(cb).hexdigest()=='e44c211efa0f124dc00414a475b2dca0d576117aaed7f4a371aa5a687be0a540'
candidate=json.loads(cb);assert candidate['source']==new and candidate['witnesses']==g['witnesses'] and candidate['fixed_numerals']==g['fixed_numerals'] and candidate['operations']==86 and candidate['exact_degree']==26
ready=set(g['witnesses']+g['fixed_numerals']);deg={x:1 for x in g['witnesses']};deg.update({x:0 for x in g['fixed_numerals']})
for n,op,a,b in new:
 assert n not in ready and all(isinstance(x,int) or x in ready for x in (a,b));da=0 if isinstance(a,int) else deg[a];db=0 if isinstance(b,int) else deg[b];deg[n]=da+db if op=='*' else max(da,db);ready.add(n)
needed={'out'}
for n,op,a,b in reversed(new):
 if n in needed:needed.update((a,b))
assert all(r[0] in needed for r in new) and all(x in needed for x in g['witnesses']+g['fixed_numerals'])
assert [deg[x] for x in ('M','ell','k','r','Bt','Y','qm','q3','U','a','c','H','shift','A0','A1','Fa','g72')]==[4,4,1,1,2,1,1,3,3,2,2,2,4,16,14,13,10]
for row in [['g30','+','ell','k'],['g31','+','g30','r'],['g32','*','M','g31'],['g33','*','Y','qm'],['g34','+','g32','g33'],['folded_q3Bt','*','q3','Bt'],['Z','-','g34','folded_q3Bt'],['g19','*','a','c'],['b0','+','X','g19'],['g58','*','U','b0'],['g59','*','H','shift'],['Dstar','+','g58','g59'],['Delta','+','H','g17']]:
 assert {r[0]:r for r in new}[row[0]]==row
# Verify both leading-cancellation identities in a free sparse polynomial ring.
def var(x):return {(x,):1}
def add(a,b):
 z=a.copy()
 for m,c in b.items():z[m]=z.get(m,0)+c
 return {m:c for m,c in z.items() if c}
def neg(a):return {m:-c for m,c in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 z={}
 for m,c in a.items():
  for n,d in b.items():
   key=tuple(sorted(m+n));z[key]=z.get(key,0)+c*d
 return {m:c for m,c in z.items() if c}
def prod(*xs):
 z={():1}
 for x in xs:z=mul(z,x)
 return z
M,ell,k,r,Bt,Y,qm,q3,U,a,c,H,shift,X=map(var,['M','ell','k','r','Bt','Y','qm','q3','U','a','c','H','shift','X'])
one={():1};two={():2};delta0=add(mul(M,add(k,r)),sub(mul(Y,qm),mul(q3,Bt)));Z=add(mul(M,ell),delta0)
A0=sub(mul(Z,Z),mul(mul(M,M),add(one,mul(ell,add(ell,k)))))
assert A0==sub(add(prod(two,M,ell,delta0),mul(delta0,delta0)),mul(mul(M,M),add(one,mul(ell,k))))
W=add(mul(U,X),mul(H,shift));Dstar=add(prod(U,a,c),W);Delta=add(mul(a,a),H)
A1=sub(mul(Dstar,Dstar),prod(U,U,add(one,prod(Delta,c,c))))
assert A1==sub(add(prod(two,U,a,c,W),mul(W,W)),prod(U,U,add(one,prod(H,c,c))))
# Local obstruction: explicit scalar data and first residual, not a full zero.
def calc(rs,inputs):
 v=dict(inputs)
 def val(x):return x if isinstance(x,int) else v[x]
 for n,op,a,b in rs:
  x,y=val(a),val(b);v[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return v
inputs={x:1 for x in g['witnesses']};inputs.update({'J':1,'F':2,'alpha':1,'X':4,'Y':256,'eta':1,'zeta':1,'r':23,'beta':3,'K0':4,'MC':1,'MF':4})
v=calc(rows,inputs);assert v['q']==4 and v['Bt']==12 and v['k']==2 and v['A0']==0 and inputs['r']-v['k']*v['Bt']==-1
assert v['E']==1024 and v['ell']==524288 and v['M']==192 and v['Z']==192*524289
assert all(v[x]!=0 for x in ('A1','Fam','g72'))
assert -524289-v['ell']-v['k']-inputs['Y']//v['q3']+v['Bt']//v['qm']==-1048579
# Exact source-level substitution holds at an integer valuation.
shifted=dict(inputs);shifted['r']=inputs['r']-v['k']*v['Bt'];vnew=calc(new,shifted);assert vnew['out']==v['out']
# Compact44-byte matching and actual modular full-graph ray.
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bind=p72/'ACTIVE_BINDING.json';br=bind.read_bytes();assert hashlib.sha256(br).hexdigest()=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf';b=json.loads(br);prime=1000000007;fixed={}
p115=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';braw=p115.read_bytes();assert hashlib.sha256(braw).hexdigest()=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';b115=json.loads(braw)
assert set(b['ports'])==set(b115['ports'])==set(g['fixed_numerals'])
for n,m in b['ports'].items():assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
for n,m in b['ports'].items():
 z=(p72/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];x=gzip.decompress(z);assert len(x)==m['raw_bytes'] and hashlib.sha256(x).hexdigest()==m['sha256_raw'];fixed[n]=int.from_bytes(x,'little')%prime
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 return trim(z)
vals={x:[0,1] for x in g['witnesses']};vals.update({n:[x] for n,x in fixed.items()})
def val(x):return [x%prime] if isinstance(x,int) else vals[x]
for n,op,a,b in new:vals[n]=mul(val(a),val(b)) if op=='*' else add(val(a),val(b),1 if op=='+' else -1)
assert len(vals['out'])-1==26 and vals['out'][-1]!=0
print(json.dumps({'parent_sha256':hashlib.sha256(raw).hexdigest(),'operations':86,'all_gates_inputs_ports_live':True,'proved_degree_upper':26,'prime':prime,'ray_degree':len(vals['out'])-1,'ray_leader':vals['out'][-1],'local_first_factor_obstruction':{'q':v['q'],'Bt':v['Bt'],'k':v['k'],'old_r':inputs['r'],'shifted_r':shifted['r'],'A0':v['A0']},'scope':'conditional ring substitution and local first-factor control; no positive-zero equivalence, Lean or PDF theorem'},sort_keys=True,indent=2))
