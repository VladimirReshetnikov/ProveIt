from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary10-divisible61-s-unshift60-universal-zero')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert 'def betaNat : ℕ := 2^(67*8807)-1' in Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
P=json.loads(Path('research/ordinary10-two-norm-divisible61/candidate.json').read_text());G=json.loads((D/'candidate.json').read_text())
assert G['source']==[(['Y','*','q3','n_s'] if r[0]=='Y' else r) for r in P['source'] if r[0]!='s']
assert G['witnesses']==P['witnesses'] and G['fixed_numerals']==P['fixed_numerals'] and G['domain']==P['domain']=='nonnegative integers' and len(G['source'])==60
# Exact polynomials in beta,w,h,MC,MF, with K0=beta*h-w-1.
z=(0,0,0,0,0)
def cn(x):return {} if x==0 else {z:x}
def var(i):a=[0]*5;a[i]=1;return {tuple(a):1}
def add(a,b):
 r=a.copy()
 for k,v in b.items():r[k]=r.get(k,0)+v
 return {k:v for k,v in r.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 r={}
 for k,v in a.items():
  for l,w in b.items():
   t=tuple(x+y for x,y in zip(k,l));r[t]=r.get(t,0)+v*w
 return {k:v for k,v in r.items() if v}
b,w,h,MC,MF=(var(i) for i in range(5));one=cn(1);q=add(b,one)
K=sub(sub(mul(b,h),w),one)
rank=add(mul(add(one,mul(b,b)),sub(mul(q,q),one)),add(MC,mul(q,MF)))
t=sub(mul(sub(b,one),add(w,h)),one)
v={'beta':b,'K0':K,'MC':MC,'MF':MF,'n_J':one,'n_F':cn(0),'n_alpha':cn(0),
   'n_w':w,'n_s':cn(0),'n_h':t,'n_tau':one,'n_eta':one,
   'n_zeta':sub(rank,one),'n_gamma':cn(0)}
for n,op,a,c in G['source']:
 assert n not in v
 a=cn(a) if isinstance(a,int) else v[a];c=cn(c) if isinstance(c,int) else v[c]
 v[n]=add(a,c) if op=='+' else sub(a,c) if op=='-' else mul(a,c)
for name,expected in {'q':q,'Y':cn(0),'U':cn(0),'ell':cn(0),'C':sub(b,one),
 'R':rank,'kbase':rank,'k':add(rank,one),'Bres':cn(0),'firstres':cn(0),
 'Dstar':cn(0),'A1':cn(0),'out':cn(0)}.items():assert v[name]==expected,name
rows={};leaves=set(G['fixed_numerals']+G['witnesses'])
for name,op,a,c in G['source']:
 assert name not in rows and all(isinstance(x,int) or x in leaves or x in rows for x in (a,c))
 rows[name]=(a,c)
live=set();used=set()
def walk(x):
 if isinstance(x,int):return
 if x not in rows:used.add(x);return
 if x in live:return
 live.add(x)
 for z in rows[x]:walk(z)
walk(G['output']);assert len(live)==60 and used==leaves
# Finite controls for the ceiling construction and natural witnesses.
for beta in range(2,20):
 for K0 in range(80):
  hv=(K0+2+beta-1)//beta;wv=beta*hv-K0-1
  assert 1<=wv<=beta and hv>=1
  tv=(beta-1)*(wv+hv)-1
  assert tv>=1 and (beta-1)*((beta+1)*wv+K0)-1==beta*tv
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'candidate_sha256':sha256((D/'candidate.json').read_bytes()).hexdigest(),
 'symbolic_ports':'K0=beta*h-w-1, arbitrary MC and MF',
 'candidate_live_operations':len(live),'candidate_live_witnesses':len(G['witnesses']),
 'all_residuals_zero_as_polynomials':True,'natural_witness_construction_for_beta_at_least_two':True,
 'actual_compact_beta_included':True,'61_graph_nonequivalence_proved':False,'lean_executed':False},indent=2,sort_keys=True))
