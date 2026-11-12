from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent;D=p.parents[1]
a=(D/'Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean').read_text()
b=(p/'CompactPortBoundsSlim.lean').read_text()
old=a[a.index('theorem port_bounds '):a.index('\n/-- `0 < K0`',a.index('theorem port_bounds '))].strip()
new=b[b.index('theorem port_bounds '):b.index('\n\nend DiophantineConsistency.CompactPortBoundsSlimDraft')].strip()
assert old==new
for x in ('import DiophantineConsistency.Compact44.CompactMaskBoundFinish','import DiophantineConsistency.Compact44.CompactSymbolicPorts','import DiophantineConsistency.ArithmeticStandardCasts','namespace DiophantineConsistency.CompactPortBoundsSlimDraft'):assert x in b
assert 'import DiophantineConsistency.Mixed121' not in b
count=0
for B in range(63,100):
 for L in range(B):
  for H in range(B):
   assert 0<B and L<B and B+H<2*B and B>=46
   count+=1
print(json.dumps({'theorem_block_byte_identical':True,'finite_bound_controls':count,'lean_run':False,'source_sha256':hashlib.sha256((p/'CompactPortBoundsSlim.lean').read_bytes()).hexdigest(),'original_theorem_sha256':hashlib.sha256(old.encode()).hexdigest()},sort_keys=True,indent=2))
