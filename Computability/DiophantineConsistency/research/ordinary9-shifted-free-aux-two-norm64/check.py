from pathlib import Path
from hashlib import sha256
import itertools,json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary9-shifted-free-aux-two-norm64')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('reviews/ordinary13-free-aux-square-general-completion-second-independent')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_text());h=json.loads((D/'candidate.json').read_text());free=json.loads(Path('research/ordinary13-shifted85-free-aux-square-criterion/candidate.json').read_text())
cut=next(i for i,r in enumerate(g['source']) if r[0]=='A1');expected=[r for r in g['source'][:cut+1] if r[0] not in ('i','T')]
expected += [['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['out','+','A0sq','A1sq']]
assert h['source']==expected and len(expected)==64 and len(h['witnesses'])==9
assert h['domain']=='nonnegative integers' and h['output']=='out' and h['fixed_numerals']==free['fixed_numerals']
# Ordered syntax of the retained norm fields is byte-for-byte the same.
for field in ('A0','A1'):
 def tree(graph,target):
  d={n:('v',n) for n in graph['witnesses']};d.update({n:('p',n) for n in graph['fixed_numerals']})
  for n,op,x,y in graph['source']:
   d[n]=(op,d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)
   if n==target:return d[n]
 assert tree(h,field)==tree(free,field)
rows={n:(op,a,b) for n,op,a,b in h['source']};live=set();inputs=set(h['witnesses']);used=set()
def visit(x):
 if isinstance(x,int):return
 if x in inputs:used.add(x)
 if x in live or x not in rows:return
 live.add(x);_,a,b=rows[x];visit(a);visit(b)
visit('out');assert len(live)==64 and used==inputs
# Generic first/main factor units can never be -1 mod 4.
for b,z,x,s,k in itertools.product(range(4),repeat=5):
 Y=(1+b)**3*s;ell=x*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4!=3
for u,a,c,d in itertools.product(range(4),repeat=4):
 assert (1+d*d-u*u*(1+(3+4*a+a*a)*c*c))%4!=3
# Formal polynomial identity for the A1 cancellation, in abstract U,X,a,c,H,S.
N=6;zero=(0,)*N
def const(x):return {zero:x} if x else {}
def var(i):
 e=[0]*N;e[i]=1;return {tuple(e):1}
def add(a,b,sign=1):
 r=a.copy()
 for k,v in b.items():r[k]=r.get(k,0)+sign*v
 return {k:v for k,v in r.items() if v}
def sub(a,b):return add(a,b,-1)
def mul(a,b):
 r={}
 for e,c0 in a.items():
  for f,d in b.items():
   k=tuple(x+y for x,y in zip(e,f));r[k]=r.get(k,0)+c0*d
 return {k:v for k,v in r.items() if v}
U,X,a,c,H,S=[var(i) for i in range(N)];one=const(1);two=const(2)
B=add(X,mul(a,c));Dstar=add(mul(U,B),mul(H,S));delta=add(H,mul(a,a))
lhs=sub(mul(Dstar,Dstar),mul(mul(U,U),add(one,mul(delta,mul(c,c)))))
rhs=add(add(mul(mul(U,U),sub(sub(add(mul(X,X),mul(two,mul(mul(X,a),c))),one),mul(H,mul(c,c)))),mul(two,mul(mul(mul(U,B),H),S))),mul(mul(H,H),mul(S,S)))
assert lhs==rhs
# Fixed-port syntactic bounds, followed by the exact cancellation identity.
deg={name:1 for name in h['witnesses']};deg.update({name:0 for name in h['fixed_numerals']})
for n,op,x,y in h['source']:
 x=deg[x] if isinstance(x,str) else 0;y=deg[y] if isinstance(y,str) else 0
 deg[n]=x+y if op=='*' else max(x,y)
assert {n:deg[n] for n in ('q','X','Y','U','a','c','H','R','shift','A0')}=={'q':1,'X':2,'Y':4,'U':6,'a':6,'c':5,'H':6,'R':4,'shift':7,'A0':24}
# The three summands in the displayed A1 identity have degrees at most
# 28, 30 and 26. A0² has degree at most 48, so output degree <=60.
U0,X0,a0,c0,H0,S0=(deg[n] for n in ('U','X','a','c','H','shift'))
terms=(2*U0+max(2*X0,X0+a0+c0,H0+2*c0),U0+max(X0,a0+c0)+H0+S0,2*H0+2*S0)
assert terms==(28,30,26) and 2*max(deg['A0'],*terms)==60
# Compute exact univariate leading coefficient in t, retaining formal beta.
def C2(x):return {(0,0):x} if x else {}
def add2(a,b,sign=1):
 r=a.copy()
 for e,c0 in b.items():r[e]=r.get(e,0)+sign*c0
 return {e:c0 for e,c0 in r.items() if c0}
def mul2(a,b):
 r={}
 for (i,j),x in a.items():
  for (k,l),y in b.items():r[(i+k,j+l)]=r.get((i+k,j+l),0)+x*y
 return {e:x for e,x in r.items() if x}
d={name:{} for name in h['witnesses']+h['fixed_numerals']};d['beta']={(0,1):1}
for name in ('n_J','n_w','n_s','n_eta','n_gamma'):d[name]={(1,0):1}
for n,op,x,y in h['source']:
 x=d[x] if isinstance(x,str) else C2(x);y=d[y] if isinstance(y,str) else C2(y)
 d[n]=add2(x,y) if op=='+' else add2(x,y,-1) if op=='-' else mul2(x,y)
for n,degree,terms in [('A1',30,{(30,21):8}),('out',60,{(60,42):64})]:
 assert max(i for i,j in d[n])==degree
 assert {key:v for key,v in d[n].items() if key[0]==degree}==terms
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'live_variables':len(used),'live_binary_operations':len(live),
 'exact_child_norm_trees':True,'first_main_unit_sign_exhaustion':True,
 'A1_cancellation_polynomial_identity':True,'degree_upper_bound_from_identity':60,
 'ray_leading_coefficient':'64*beta^42','exact_degree_for_beta_nonzero':60,
 'standard_zero_equivalent_to_shifted_free_aux_child_for_natural_ports':True,
 'shifted_parent_reverse_bridge_proved':False,'lean_executed':False},sort_keys=True,indent=2))
