#!/usr/bin/env python3
from pathlib import Path
from itertools import product
from collections import Counter
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-five-unit-modfour-client-draft'
pins={'README.md':'342609a19e94933b0f194a13e6cc02f6daf90c5b1233617ffda2d59124ea6cdc','FiveUnitModFour.lean':'95d74abebdd375bda494ab5f279670226602ac5a5f854f4ed01f8aee0a979c00','check_source.py':'f7e6969e7a943208dcd7c79c7dfaddfcdf27b41ffd7d89d6fef7eb0444e16c85','observation.json':'42a4e70d652d29021f11db7cedb82c7cb73101b8231bf4f941886292174cf938'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
tail=b'\nIndependent source review: [five-unit mod-four client](../../reviews/ordinary14-five-unit-modfour-client-independent/README.md).\n'
final_readme='dabfeec0c655bda58291a1693ac1f64739b889cfa98ea9549e84e67b54062a55'
readme=(A/'README.md').read_bytes()
assert hashlib.sha256(readme).hexdigest()==final_readme
assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()==pins['README.md']
for n,v in pins.items():
 if n!='README.md':assert sha(A/n)==v,(n,sha(A/n))
source=(A/'FiveUnitModFour.lean').read_text();dep=(D/'research/ordinary14-five-unit-model-facts-draft/FiveUnitFacts.lean').read_text();bad=(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean').read_text()
assert sha(D/'research/ordinary14-five-unit-model-facts-draft/FiveUnitFacts.lean')=='bcded9dea0ef6a42847fa927b9be360cda30d7cec13e4969788ef93dbcf8e926'
assert sha(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.lean')=='9e80ae52f5dddd21d50684ebb6ca6556e95ac37905277bc476d251b7bf59f5a4'
for t in ['(hm : 2≤m)','(hp : Equivalent (product5 (x*x,(m*k)*(m*k+k)) q r s t) (natural (1:V)))','(hq : pairResidue q=1+d^2-u^2*(1+(a^2+4*a+3)*c^2))','(hr : pairResidue r=(a^2+4*a+3)*(f^2-1)*v^2+','(ht : pairResidue t=1+i^2-(a^2+4*a+3)*(f^2-1))','five_positive_of_direct_first m x k hm q r s t hp','rw [hq]; exact main_bad u a c d','rw [hr]; exact aux_bad a f v y','rw [ht]; exact strong_bad a f i']:
 assert t in source,t
for t in ['theorem five_positive_of_direct_first','(hq : pairResidue q ≠ -1)','(hr : pairResidue r ≠ -1)','(ht : pairResidue t ≠ -1)']:
 assert t in dep,t
for t in ['theorem main_bad : ∀ u a c d : ZMod 4','theorem strong_bad : ∀ a f i : ZMod 4','theorem aux_bad : ∀ a f v y : ZMod 4']:
 assert t in bad,t
# Derive the possible squares and coefficient classes independently, then
# evaluate every combination from the smaller value sets (not the source loops).
squares={x*x%4 for x in range(4)};deltas={(a*a+4*a+3)%4 for a in range(4)}
coeff={(d*(f-1))%4 for d in deltas for f in squares}
assert squares=={0,1} and deltas=={0,3} and coeff=={0,1}
main=Counter((1+d-u*(1+delta*c))%4 for u,d,c,delta in product(squares,squares,squares,deltas))
aux=Counter((q*v+(1-q)*y)%4 for q,v,y in product(coeff,squares,squares))
strong=Counter((1+i-q)%4 for i,q in product(squares,coeff))
assert 3 not in main and 3 not in aux and 3 not in strong
# Confirm the source aux form is the literal y² - Q(y²-v²), over every residue.
for a,f,v,y in product(range(4),repeat=4):
 Q=(a*a+4*a+3)*(f*f-1)
 assert (Q*v*v+(1-Q)*y*y-y*y+Q*(y*y-v*v))%4==0
result=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True)
assert result.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'independent source-signature and finite mod-four review; no Lean or graph-binding claim','main_residue_histogram':dict(sorted(main.items())),'aux_residue_histogram':dict(sorted(aux.items())),'strong_residue_histogram':dict(sorted(strong.items())),'aux_identity_cases':256,'author_receipt_replayed':True,'author_source_sha256':pins['FiveUnitModFour.lean'],'reviewed_readme_sha256':pins['README.md']},sort_keys=True,indent=2))
