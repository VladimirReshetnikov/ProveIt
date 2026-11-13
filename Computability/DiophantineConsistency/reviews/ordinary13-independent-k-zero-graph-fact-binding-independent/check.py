from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-zero-graph-fact-binding-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P0=Path('research/ordinary13-independent-k-zero-graph-fact-binding-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P0/'check.py')])==(P0/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());s=Path('research/ordinary13-independent-k-unit-norm-draft/IndependentKUnitGraph.lean.src').read_text()
assert len(g['source'])==84 and g['witnesses'][10]=='n_k'
for i,n in enumerate(g['witnesses']):assert f'  let {n} : Expr (Fin 13) := .var {i}\n' in s
for i,n in enumerate(g['fixed_numerals']):assert f'  let {n} : Expr (Fin 13) := .constant (p {i})\n' in s
for n,op,x,y in g['source']:assert f'  let {n} := {x} {op} {y}\n' in s
assert '⟨A0, A1, Fa, Fs, out, g72, qm, Z, X, s, n_k, U, a, c, Dstar, n_y, V, n_f, I, ell, Delta⟩' in s
# Exact commutative-ring polynomial replay through the actual main residual at k=0.
# Inputs unrelated to the first/main field are set to 0; all remaining
# independent inputs and four ports are free indeterminates.
names=['n_J','n_F','n_alpha','n_w','n_s','n_r','n_eta','n_gamma','beta','K0','MC','MF'];N=len(names);zero=(0,)*N
class Poly:
 def __init__(self,d):self.d={k:v for k,v in d.items() if v}
 def __add__(self,o):
  o=pol(o);r=self.d.copy()
  for k,v in o.d.items():r[k]=r.get(k,0)+v
  return Poly(r)
 __radd__=__add__
 def __neg__(self):return Poly({k:-v for k,v in self.d.items()})
 def __sub__(self,o):return self+-pol(o)
 def __rsub__(self,o):return pol(o)+-self
 def __mul__(self,o):
  o=pol(o);r={}
  for k,v in self.d.items():
   for j,w in o.d.items():
    key=tuple(a+b for a,b in zip(k,j));r[key]=r.get(key,0)+v*w
  return Poly(r)
 __rmul__=__mul__
 def __eq__(self,o):return self.d==pol(o).d
def pol(x):return x if isinstance(x,Poly) else Poly({zero:x})
def var(i):
 e=[0]*N;e[i]=1;return Poly({tuple(e):1})
deps={n:{n} for n in g['witnesses']+g['fixed_numerals']}
for name,op,x,y in g['source']:
 deps[name]=(deps[x] if isinstance(x,str) else set()) | (deps[y] if isinstance(y,str) else set())
assert (deps['A0']|deps['A1']) <= set(names)|{'n_k'}
d={n:pol(0) for n in g['witnesses']+g['fixed_numerals']}
for i,n in enumerate(names):d[n]=var(i)
for name,op,x,y in g['source']:
 x=d[x] if isinstance(x,str) else pol(x);y=d[y] if isinstance(y,str) else pol(y)
 d[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 if name=='A1':break
J,F0,alpha0,w,s0,r,eta,gamma,beta,K,MC,MF=(d[n] for n in names)
b=beta*J;q=b+1;X=q*w;Y=q*q*q*(s0+1);U=Y*q*q;C=q-(F0+1)-(alpha0+1);B=C*(X+K)-(F0+1)
R=(alpha0+1+(q-(F0+1))*b)*(q*q-1)+J*(MC+q*MF);a=X*Y+Y;H=3+4*a
Z=b*r-B;main=U*(X+a*eta)+H*(U*gamma+R+1)
for name,want in [('qm',b),('q',q),('X',X),('Y',Y),('U',U),('ell',0),('Z',Z),('A0',Z*Z-b*b),('R',R),('Dstar',main),('A1',main*main-U*U*(1+(H+a*a)*eta*eta))]:assert d[name]==want,name
src=(P0/'IndependentKZeroGraphFacts.lean.src').read_text();client=Path('research/ordinary13-independent-k-fixed-compact-port-client-draft/IndependentKFixedCompactPorts.lean.src').read_text()
for t in ['(hk : v 10=0)','(hR : rankRing v=ι R)','IndependentKUnitBridgeDraft.signed_norms intPorts v hz','have hJ := child_J_positive v hz','rw [hR] at hshape','zero_k_fact_cut v (q v) R (X v) (Y v)']:
 assert t in src,t
for t in ['def natPorts : Fin 4 → ℕ := C44Short15Facts.c44','def intPorts : Fin 4 → ℤ := fun j => (natPorts j : ℤ)','(hrank : (ι R : DiffRing V)=','(hshape : let a:=X*Y+Y','(hnorm : let a:=X*Y+Y']:
 assert t in client,t
bridge=Path('research/ordinary13-independent-k-unit-norm-draft/IndependentKUnitBridge.lean.src').read_text()
assert 'theorem signed_norms (p : Fin 4 → ℤ) (v : Fin 13 → V)' in bridge
assert 'z*z=b*b*(1+ell*(ell+k)) ∧' in bridge
assert 'd*d=U*U*(1+Delta*(c*c)) ∧' in bridge
print(json.dumps({'all_generated_child_rows_and_fields_checked':True,'exact_first_main_rank_polynomials_at_k0_checked':True,'same_fixed_tuple_and_valuation_checked':True,'rank_natural_representation_explicit':True,'author_receipt_reproduced':True,'main_polynomial_terms':len(main.d),'lean_executed':False,'scope':'Unelaborated source, cast and provider review only; no rank representation or endpoint established.'},sort_keys=True,indent=2))
