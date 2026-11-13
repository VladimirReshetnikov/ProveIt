#!/usr/bin/env python3
"""Generate a candidate Lean aggregation of all bounded range certificates."""
from pathlib import Path
from hashlib import sha256
import json
H=Path(__file__).resolve().parent;mf=H/'coverage-manifest-v2.json'
if sha256(mf.read_bytes()).hexdigest()!='d0847a6276885e969d06cf6c2f3f64b1de1f1cfba71095e35c33393630a57392':raise ValueError('manifest changed')
records=json.loads(mf.read_text())['records'];out=H/'DirectBFSCoverageAggregate.lean'
if out.exists():raise ValueError('refuse overwrite')
s=''.join('import '+r['module']+'\n' for r in records)
s+='import DirectBFSConjugacyShape\nset_option autoImplicit false\nset_option Elab.async false\nset_option maxRecDepth 16384\nset_option maxHeartbeats 30000000\nnamespace DirectBFSCoverageAggregate\nopen DirectBFSConjugacyChunk DirectBFSCoverage DirectBFSConjugacyBase\n'
checks={
 'rows':('checkRows',943,None), 'inverse':('checkRowInverse',943,None),
 'horizontal':('checkHorizontal',250,None), 'vertical':('checkVertical',439,None),
 'inversebounds':(None,943,'fun j => decide (rowMap.getD j 0 < 943 ∧ rowInverse.getD j 0 < 943)'),
 'horizontalbounds':(None,250,'fun j => decide (horizontal.getD j 0 < 250 ∧ horizontalInverse.getD j 0 < 250)'),
 'verticalbounds':(None,439,'fun j => decide (vertical.getD j 0 < 439 ∧ verticalInverse.getD j 0 < 439)')}
for kind,(fn,end,pred) in checks.items():
 seg=[(r['index'],x['start'],x['count']) for r in records for x in r['ranges'] if x['kind']==kind]
 if [j for _,a,n in seg for j in range(a,a+n)]!=list(range(end)):raise ValueError('coverage mismatch '+kind)
 goal=f'{fn} 0 {end}=true' if fn else f"(List.range' 0 {end}).all ({pred})=true"
 s+=f'\ntheorem {kind}_all : {goal} := by\n'
 for i,a,n in seg:s+=f'  have h{i:03d} := DirectBFSCoverage.{kind}_{i:03d}\n'
 if fn:
  s+='  unfold '+fn+' at '+' '.join(f'h{i:03d}' for i,_,_ in seg)+' ⊢\n'
 terms=[f"List.range' {a} {n}" for _,a,n in seg];expr=terms[0]
 for term in terms[1:]:expr=f'({expr} ++ {term})'
 s+=f"  have hr : List.range' 0 {end}={expr} := by\n    simp only [List.range'_append_1, Nat.reduceAdd]\n"
 s+='  rw [hr]\n  simp only [List.all_append, '+', '.join(f'h{i:03d}' for i,_,_ in seg)+', Bool.true_and]\n'
for kind in checks:s+=f'#print axioms DirectBFSCoverageAggregate.{kind}_all\n'
s+='end DirectBFSCoverageAggregate\n';out.write_text(s)
print('generated aggregate source; compilation depends on the full sweep')
