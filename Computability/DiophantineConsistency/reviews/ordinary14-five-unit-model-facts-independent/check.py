from pathlib import Path
from itertools import product
from math import isqrt
import hashlib,json,subprocess,sys
D=Path(__file__).resolve().parents[2]
A=D/'research/ordinary14-five-unit-model-facts-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths={'draft':A/'FiveUnitFacts.lean','pell':D/'Lean/DiophantineConsistency/ArithmeticNegativeNorms.lean','pairs':D/'Lean/DiophantineConsistency/ArithmeticSignedPairs.lean','residue':D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean'}
s={k:p.read_text() for k,p in paths.items()}
def compact(s):return ''.join(s.split())
pell=compact(s['pell']);pairs=compact(s['pairs']);residue=compact(s['residue']);draft=compact(s['draft'])
for token in ['theoremconsecutive_ne_negative(nx y:V)(hn:2≤n):x*x+1≠n*(n+1)*y*y'.replace(' ', '')]:assert token in pell
assert 'defEquivalent(pq:PairV):Prop:=p.1+q.2=p.2+q.1' in pairs
assert 'theoremproduct5_positive{pqr st:PairV}(h:Equivalent(product5pqrst)(natural(1:V)))(hp:p.1+1≠p.2)(hq:q.1+1≠q.2)(hr:r.1+1≠r.2)(ht:t.1+1≠t.2)'.replace(' ','') in pairs
assert 'defpairResidue(p:PairV):ZMod4:=residuep.1-residuep.2' in residue
assert 'theoremnegative_residue{p:PairV}(h:p.1+1=p.2):pairResiduep=-1' in residue
for token in ['(hm:2≤m)','Equivalent(product5(x*x,(m*k)*(m*k+k))qrst)(natural(1:V))','(hq:pairResidueq≠-1)','(hr:pairResiduer≠-1)','(ht:pairResiduet≠-1)','s.1=s.2+1','ArithmeticNegativeNorms.consecutive_ne_negativemxkhm','applyproduct5_positivehp(first_ne_negativemxkhm)']:
 assert token in draft,token
assert 'import DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011' in s['residue']
assert 'import DiophantineConsistency.ArithmeticSignedPairs' in (D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorMagnitude2011.lean').read_text()
assert 'import DiophantineConsistency.ModelArithmetic' not in s['draft']
# The fact-level identity and first-unit exclusion, including the sharp m=1 failure.
assert 1*1+1 == (1*1)*(1*1+1)
count=0
for m,k in product(range(2,81),range(101)):
 assert (m*k)*(m*k+k)==m*(m+1)*k*k
 n=m*(m+1)*k*k-1
 assert n<0 or isqrt(n)**2!=n
 count+=1
# Independent signed-pair semantics, including four sign-exclusion necessity witnesses.
def mul(p,q):return (p[0]*q[0]+p[1]*q[1],p[0]*q[1]+p[1]*q[0])
def product5(ps):
 v=ps[0]
 for p in ps[1:]:v=mul(v,p)
 return v
vals=list(product(range(3),repeat=2)); accepted=0;guard_negative=0;witness={i:False for i in (0,1,2,4)}
for ps in product(vals,repeat=5):
 p=product5(ps)
 if p[0]!=p[1]+1:continue
 diff=[a-b for a,b in ps]
 if diff[3]==-1:guard_negative+=1
 for i in witness:
  if diff[i]==-1 and diff[3]==-1 and all(diff[j]==1 for j in witness if j!=i):witness[i]=True
 if diff[0]!=-1 and all(diff[i]%4!=3 for i in (1,2,4)):
  assert all(z==1 for z in diff)
  accepted+=1
assert accepted and guard_negative and all(witness.values())
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],capture_output=True,text=True,check=True)
assert json.loads(r.stdout)==json.loads((A/'observation.json').read_text())
print(json.dumps({'author_readme_sha256':sha(A/'README.md'),'author_checker_sha256':sha(A/'check_source.py'),'author_observation_sha256':sha(A/'observation.json'),'source_sha256':{k:sha(p) for k,p in paths.items()},'negative_pell_cases':count,'m_one_negative_unit_counterexample':True,'pair_assignments':len(vals)**5,'positive_product_cases_satisfying_exclusions':accepted,'negative_guard_with_product_one_cases':guard_negative,'each_of_four_exclusions_has_a_sign_witness':all(witness.values()),'author_receipt_replayed':True,'lean_run':False},sort_keys=True,indent=2))
