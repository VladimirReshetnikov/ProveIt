from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-eta-zeta84-unshift-s-full-zero-independent');A=Path('research/ordinary13-eta-zeta84-unshift-s-full-zero')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
p=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text());g=json.loads((A/'probe.json').read_text())
assert len(p['source'])==85 and len(g['source'])==84
expected=[]
for r in p['source']:
 if r==['s','+','n_s',1]:continue
 expected.append(['n_s' if x=='s' else x for x in r])
assert expected==g['source'] and p['witnesses']==g['witnesses'] and p['fixed_numerals']==g['fixed_numerals']
# Independent exact sparse polynomials in formal beta,w,h,MC,MF.
Z=(0,)*5
def P(x):return {(0,)*5:x} if x else {}
def var(i):
 e=[0]*5;e[i]=1;return {tuple(e):1}
def add(x,y,sign=1):
 d=x.copy()
 for k,n in y.items():d[k]=d.get(k,0)+sign*n
 return {k:n for k,n in d.items() if n}
def mul(x,y):
 d={}
 for a,b in x.items():
  for c,e in y.items():
   k=tuple(i+j for i,j in zip(a,c));d[k]=d.get(k,0)+b*e
 return {k:n for k,n in d.items() if n}
def sub(x,y):return add(x,y,-1)
beta,w,h,MC,MF=[var(i) for i in range(5)];one=P(1);q=add(beta,one);K=sub(sub(mul(beta,h),w),one)
R=add(add(mul(add(one,mul(beta,beta)),sub(mul(q,q),one)),MC),mul(q,MF));k=add(R,one)
t=sub(mul(sub(beta,one),add(w,h)),one);B=mul(beta,t);rr=add(add(mul(k,sub(B,one)),t),one)
ws=[one,{}, {},P(2),P(2),sub(R,one),w,{},rr,one,R,one,{}];ps=[beta,K,MC,MF]
d=dict(zip(g['witnesses'],ws));d.update(zip(g['fixed_numerals'],ps))
for name,op,a,b in g['source']:
 x=d[a] if isinstance(a,str) else P(a);y=d[b] if isinstance(b,str) else P(b)
 d[name]={'+':lambda:add(x,y),'-':lambda:sub(x,y),'*':lambda:mul(x,y)}[op]()
for name,value in [('q',q),('Y',{}),('U',{}),('ell',{}),('c',one),('R',R),('kbase',k),('Bt',B),('Z',beta),('Dstar',{}),('Q',P(9)),('I',P(3)),('V',P(-1)),('A0',{}),('A1',{}),('g72',{}),('Fa',one),('out',{})]:assert d[name]==value,name
# Natural constraints, ceiling and actual graph evaluated exactly.
cases=0
for beta0 in range(2,18):
 for K0 in range(40):
  h0=(K0+2+beta0-1)//beta0;w0=beta0*h0-K0-1;q0=beta0+1
  assert h0>=1 and 1<=w0<=beta0
  for MC0,MF0 in ((0,0),(1,2),(9,4)):
   R0=(1+beta0**2)*(q0**2-1)+MC0+q0*MF0;k0=R0+1;t0=(beta0-1)*(w0+h0)-1;B0=beta0*t0;r0=k0*(B0-1)+t0+1
   v=[1,0,0,2,2,R0-1,w0,0,r0,1,R0,1,0];ports=[beta0,K0,MC0,MF0]
   assert t0>=1 and B0>=2 and min(v)>=0
   env=dict(zip(g['witnesses'],v));env.update(zip(g['fixed_numerals'],ports))
   for name,op,a,b in g['source']:
    x=env[a] if isinstance(a,str) else a;y=env[b] if isinstance(b,str) else b
    env[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
   assert (env['A0'],env['A1'],env['g72'],env['Fa'],env['out'])==(0,0,0,1,0)
   cases+=1
beta_src=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text();ports_src=Path('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta_src
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports_src
print(json.dumps({'author_receipt_reproduces':True,'exact_full_graph_sparse_polynomial_zero':True,'natural_ceiling_witness_controls':cases,'compact_tuple_source_expression_checked':True,'toy_parent_same_vector_only':True,'lean_executed':False,'zero_set_inequivalence_proved':False},sort_keys=True,indent=2))
