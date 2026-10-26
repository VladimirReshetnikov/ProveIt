#!/usr/bin/env python3
"""Regenerate source-only candidate files and patches. No Lean invocation."""
from pathlib import Path
import difflib,hashlib,json
R=Path(__file__).resolve().parents[1]
S=R/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency'
OUT=R/'local_candidates'
changes={
'WangTiles942PhysicalOrder.lean':[(
(S/'WangTiles942PhysicalOrder.lean').read_text().split('    (i : Fin n) : f i = i := by\n',1)[1].split('\ndef rankMap',1)[0],
'''  let e : Fin n ≃o Fin n :=
    ⟨Equiv.ofBijective f ⟨hf.injective, Finite.surjective_of_injective hf.injective⟩,
      hf.le_iff_le⟩
  exact Fin.ext (Fin.coe_orderIso_apply e i)
''')],
'IterationSize.lean':[(
'''    (DirectGraphEnumerator.iterate p initial).depth = (rows p initial).depth := by
  have he : (DirectGraphEnumerator.iterate p initial).expression = (rows p initial).expression := rfl
  exact congrArg Expr.depth he''',
'''    (DirectGraphEnumerator.iterate p initial).depth = (rows p initial).depth := rfl''')],
'SidonPositions.lean':[(
'''  intro i j h
  have hp : weight m i + weight m 0 = weight m j + weight m 0 := by rw [h]
  rcases (weight_sum_eq_iff i 0 j 0).mp hp with h | h
  · exact h.1
  · exact h.1.trans h.2''',
'''  intro i j h
  rcases (weight_sum_eq_iff i i j j).mp (congrArg (fun n => n + n) h) with h | h <;>
    exact h.1'''),(
'''  · have hi : p.val.1 = q.val.1 := by
      apply le_antisymm
      · simpa only [h2] using p.property
      · simpa only [← h1] using q.property
    have hj : p.val.2 = q.val.2 := h2.trans (hi.symm.trans h1)
    exact Subtype.ext (Prod.ext hi hj)''',
'''  · have hp := p.property
    have hq := q.property
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> omega''')]
}
rows=[]
for name,replacements in changes.items():
 a=(S/name).read_text();b=a
 for old,new in replacements:
  if b.count(old)!=1:raise ValueError(f'Expected unique source anchor: {name}')
  b=b.replace(old,new)
 (OUT/'candidate'/name).write_text(b)
 rel=f'Computability/DiophantineConsistency/Lean/DiophantineConsistency/{name}'
 (OUT/'patches'/(name+'.patch')).write_text(''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel)))
 rows.append({'file':name,'source_lines':len(a.splitlines()),'candidate_lines':len(b.splitlines()),'net_lines_saved':len(a.splitlines())-len(b.splitlines()),'source_sha256':hashlib.sha256(a.encode()).hexdigest(),'candidate_sha256':hashlib.sha256(b.encode()).hexdigest(),'status':'UNCOMPILED'})
(OUT/'metrics.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
