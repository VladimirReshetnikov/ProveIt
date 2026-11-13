from pathlib import Path
from hashlib import sha256
import json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-j-positive-source-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-independent-k-j-positive-model-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text())
r={n:(op,a,b) for n,op,a,b in g['source']}
assert g['witnesses'][:3]==['n_J','n_F','n_alpha'] and g['witnesses'][6]=='n_w'
assert g['fixed_numerals'][1]=='K0'
# Independently evaluate graph expressions symbolically at J=0 with a sparse
# integer polynomial in F-slot, alpha-slot, w-slot, K0-port.
N=4;zero=(0,)*N
def c(x):return {zero:x} if x else {}
def var(i):
 e=[0]*N;e[i]=1;return {tuple(e):1}
def add(a,b,sgn=1):
 d=a.copy()
 for e,v in b.items():d[e]=d.get(e,0)+sgn*v
 return {e:v for e,v in d.items() if v}
def mul(a,b):
 d={}
 for e,v in a.items():
  for f,w in b.items():
   key=tuple(x+y for x,y in zip(e,f));d[key]=d.get(key,0)+v*w
 return {e:v for e,v in d.items() if v}
known={'n_J':{},'n_F':var(0),'n_alpha':var(1),'n_w':var(2),'K0':var(3)}
def ev(x):
 if isinstance(x,int):return c(x)
 if x in known:return known[x]
 op,a,b=r[x];aa=ev(a)
 if op=='*' and not aa:out={}
 else:
  bb=ev(b);out={'+':lambda:add(aa,bb),'-':lambda:add(aa,bb,-1),'*':lambda:mul(aa,bb)}[op]()
 known[x]=out;return out
one=c(1);F=add(var(0),one);alpha=add(var(1),one);C=add(add(one,F,-1),alpha,-1)
Z=add(F,mul(C,add(var(2),var(3))),-1)
assert ev('qm')=={} and ev('q')==one and ev('X')==var(2) and ev('Z')==Z
assert ev('A0')==mul(Z,Z)
s=(p/'IndependentKJPositive.lean.src').read_text();bridge=Path('research/ordinary13-independent-k-unit-norm-draft/IndependentKUnitBridge.lean.src').read_text()
assert '(p : Fin 4 → ℕ)' in s and '(hz : InternalZero (graph (fun j => (p j:ℤ))).output v)' in s
for text in ('P72Root.cast_port','have hj : v 0=0','have hZpos','IndependentKUnitBridgeDraft.signed_norms pp v hz','mul_self_eq_zero.mp hsquare'):
 assert text in s,text
assert 'z*z=b*b*(1+ell*(ell+k)) ∧' in bridge
cast=Path('Lean/DiophantineConsistency/Compact44/P72Root.lean').read_text()
assert 'theorem cast_port (p : Fin 4 → ℕ) (j : Fin 4)' in cast
# Bounded numeric positivity controls, with arbitrary nonnegative K0.
for F0 in range(7):
 for A0 in range(7):
  for w in range(7):
   for K in range(7):
    assert F0+1-(1-(F0+1)-(A0+1))*(w+K)>0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_checker_reproduced':True,'exact_J_zero_first_root_polynomial':True,
 'first_residual_is_root_square_at_J_zero':True,'natural_port_and_norm_interfaces_observed':True,
 'finite_positivity_controls':2401,'lean_executed':False,'elaboration_or_provider_validation':False},sort_keys=True,indent=2))
