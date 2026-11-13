from pathlib import Path
from hashlib import sha256
import json,sys,re
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-explicit-pell-period-model-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
source=Path('Lean/DiophantineConsistency/ArithmeticPellSquaredSeed.lean').read_text()
rec=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
draft=Path('research/ordinary13-explicit-pell-period-model-draft/ExplicitPellPeriod.lean.src').read_text()
assert 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in source
assert 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in draft
sig=re.search(r'theorem doubled_quotients \(n R a : V\)\s*:\s*(.*?)\s*:= by',source,re.S).group(1)
assert re.sub(r'\s+','',sig)=='∃rs:V,xcoord(2*n*R)a=1+ycoordRa*ycoordRa*r∧ycoord(2*n*R)a=2*n*xcoordRa*ycoordRa+ycoordRa*ycoordRa*s'
assert 'doubled_quotients (ycoord m a) m a' in draft
assert 'refine ⟨r, 2*xcoord m a+s, ?_, ?_⟩' in draft
assert 'rw [show 2*m*ycoord m a = 2*ycoord m a*m by ring]' in draft
assert 'rw [show 2*m*ycoord m a = 2*ycoord m a*m by ring, hy] <;> ring' in draft
assert 'import DiophantineConsistency.ArithmeticPellSquaredSeed' in draft
assert 'import Mathlib.Tactic.Ring' in rec
assert 'def delta (b : V) : V := (b+1)*(b+3)' in rec
assert '(b+2)*π₁ previous+delta b*π₂ previous' in rec
assert 'π₁ previous+(b+2)*π₂ previous' in rec
assert 'theorem time_le_y (time b : V) : time≤ycoord time b' in rec
# Check both displayed polynomial identities using sparse formal monomials.
def add(x,y):
 z=x.copy()
 for a,b in y.items():z[a]=z.get(a,0)+b
 return {a:b for a,b in z.items() if b}
def mul(x,y):
 z={}
 for a,b in x.items():
  for c,d in y.items():
   k=tuple(i+j for i,j in zip(a,c));z[k]=z.get(k,0)+b*d
 return {a:b for a,b in z.items() if b}
c={(1,0,0,0):1};d={(0,1,0,0):1};s={(0,0,1,0):1};m={(0,0,0,1):1};two={(0,0,0,0):2}
assert mul(mul(two,m),c)==mul(mul(two,c),m)
assert add(mul(mul(mul(two,c),d),c),mul(mul(c,c),s))==mul(mul(add(mul(two,d),s),c),c)
# Bounded direct recurrence confirms the claim including m=0, with natural quotients.
count=0
for a in range(5):
 A=a+2;delta=(a+1)*(a+3);x,c=1,0
 for t in range(5):
  if t: x,c=A*x+delta*c,x+A*c
  h=2*t*c;xh,yh=1,0
  for _ in range(h):xh,yh=A*xh+delta*yh,xh+A*yh
  if c==0:assert t==0 and xh==1 and yh==0
  else:assert (xh-1)%(c*c)==0 and yh%(c*c)==0
  count+=1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'theorem_hypotheses_and_signature_checked':True,'index_and_coefficient_polynomials_checked':True,
 'bounded_controls_including_zero_index':count,'lean_elaboration_checked':False,
 'model_to_ipra_proof_existence_checked':False,'lean_executed':False},indent=2,sort_keys=True))
