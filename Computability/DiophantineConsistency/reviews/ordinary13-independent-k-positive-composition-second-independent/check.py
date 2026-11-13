from pathlib import Path
from hashlib import sha256
import json,re,subprocess,sys,itertools
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-positive-composition-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-independent-k-positive-composition-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
s=(p/'IndependentKPositiveComposition.lean.src').read_text();flat=lambda t:re.sub(r'\s+',' ',t)
for x in ('theorem rankRing_eq_expr','theorem rank_represented','theorem k_positive',
 'have hJ := child_J_positive v hz','obtain ⟨hb,_,_,_⟩ := bounds (V:=V)',
 'have hf := first_norm v hz hk','rw [rankRing_eq_expr v]',
 'simpa only [intPorts,emb] using hrank'):
 assert x in s,x
for x in ('(q v) (natPorts 0:V) (v 0) (v 1+1) (v 2+1) (X v+(natPorts 1:V)) (v 8) rfl hb hJ hF hf',
 'IndependentKRankRepresentationDraft.rank_representation natPorts v hFq\'',
 '(Residue90GraphNormsDraft.rank natPorts v) hz hk (rank_represented v hz hk)'):
 assert flat(x) in flat(s),x
g=Path('research/ordinary13-independent-k-zero-graph-fact-binding-draft/IndependentKZeroGraphFacts.lean.src').read_text()
for x in ('def q (v : Fin 13 → V) : V := (natPorts 0:V)*v 0+1',
 'def X (v : Fin 13 → V) : V := q v*v 6',
 '(hR : rankRing v=ι R)',
 'theorem first_norm (v : Fin 13 → V)',
 '(hz : InternalZero (graph intPorts).output v) (hk : v 10=0)'):
 assert x in g,x
r=Path('research/ordinary13-independent-k-rank-representation-draft/IndependentKRankRepresentation.lean.src').read_text()
for x in ('theorem first_norm_F_lt_q','theorem rank_representation','  linear_combination h'):
 assert x in r,x
old=Path('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src').read_text()
assert 'ι (rank p v) =\n      (ι (v 2+1)' in old
assert 'likely needs the opposite equality orientation' in (p/'README.md').read_text()
# Independent exact polynomial normalizer over six formal inputs.
N=6;z=(0,)*N
def constant(n):return {z:n} if n else {}
def var(i):
 e=[0]*N;e[i]=1;return {tuple(e):1}
def add(a,b,sign=1):
 out=a.copy()
 for k,v in b.items():out[k]=out.get(k,0)+sign*v
 return {k:v for k,v in out.items() if v}
def mul(a,b):
 out={}
 for e,c in a.items():
  for f,d in b.items():
   k=tuple(x+y for x,y in zip(e,f));out[k]=out.get(k,0)+c*d
 return {k:v for k,v in out.items() if v}
def sub(a,b):return add(a,b,-1)
one=constant(1);J,F,A,beta,MC,MF=[var(i) for i in range(N)]
b=mul(beta,J);q=add(b,one);q0=add(one,mul(J,beta))
rr1=add(mul(add(A,mul(sub(q,F),b)),sub(mul(q,q),one)),mul(J,add(MC,mul(q,MF))))
rr2=add(mul(add(A,mul(sub(q0,F),mul(J,beta))),sub(mul(q0,q0),one)),mul(J,add(MC,mul(MF,q0))))
assert rr1==rr2
# Explicit helper and client orientation: h: A=E, target E=A; using +h
# leaves E+E=A+A in mathlib's eq_of_eq, not a ring identity.
assert 1+1 != 0+0
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'child_port_valuation_and_call_interfaces':True,
 'rank_ring_polynomial_identity':True,'known_reverse_orientation_hazard_exposed':True,
 'lean_executed':False,'elaboration_or_provider_validation':False},sort_keys=True,indent=2))
