#!/usr/bin/env python3
"""Generate bounded in-Lean vector/list linkage drafts from audited literal blocks."""
import ast,hashlib,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;R=P.parent;tile=R/'nine-sharing-sign17-k-tile-coefficients-check/src/DiophantineConsistency';control=R/'nine-sharing-sign17-k-control-blocks-check/src/DiophantineConsistency/Sign17KControlBlocks.lean'
fmt=lambda xs:'['+', '.join(map(str,xs))+']'
def vals(p):
 s=p.read_text();m=re.search(r'def literal : Fin (\d+) → ℕ := !\[(.*?)\]',s,re.S);assert m
 a=ast.literal_eval('['+m.group(2)+']');assert len(a)==int(m.group(1));return a
for g in range(8):
 out=['import DiophantineConsistency.Sign17KStreamBump','','/-! SOURCE ONLY. Literal-vector to list block links. -/','set_option autoImplicit false','set_option maxRecDepth 10000','set_option maxHeartbeats 4000000','noncomputable section',f'namespace DiophantineConsistency.Sign17KCoefficientLists{g:02d}','']
 for k in (2*g,2*g+1):
  ns=f'Sign17KTileCoefficients{k:02d}';a=vals(tile/(ns+'.lean'));out += [f'theorem block{k:02d} :',f'    List.ofFn {ns}.literal = {fmt(a)} := by','  decide +kernel','']
 if g==0:
  a=vals(control);out += ['theorem control :',f'    List.ofFn Sign17KControlBlocks.literal = {fmt(a)} := by','  decide +kernel','']
 out += [f'end DiophantineConsistency.Sign17KCoefficientLists{g:02d}']+[f'#print axioms DiophantineConsistency.Sign17KCoefficientLists{g:02d}.block{k:02d}' for k in (2*g,2*g+1)]
 if g==0:out += ['#print axioms DiophantineConsistency.Sign17KCoefficientLists00.control']
 (P/f'Sign17KCoefficientLists{g:02d}.lean').write_text('\n'.join(out)+'\n')
print('SOURCE_ONLY 16 tile block and one control vector/list identities')
