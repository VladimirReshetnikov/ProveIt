#!/usr/bin/env python3
"""Draft bounded reverse-list fixtures from audited coefficient list sources."""
import re,ast,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;R=P.parent;src=R/'nine-sharing-sign17-k-coefficient-lists-draft';fmt=lambda xs:'['+', '.join(map(str,xs))+']'
for g in range(8):
 n=f'Sign17KCoefficientLists{g:02d}';s=(src/(n+'.lean')).read_text();out=[f'import DiophantineConsistency.{n}','','/-! SOURCE ONLY. Bounded reversal of audited numeric coefficient lists. -/','set_option autoImplicit false','set_option maxRecDepth 10000','noncomputable section',f'namespace DiophantineConsistency.Sign17KCoefficientReversed{g:02d}','']
 names=[f'block{k:02d}' for k in (2*g,2*g+1)]+(['control'] if g==0 else [])
 for name in names:
  m=re.search(r'theorem '+name+r' :\s*List.ofFn ([A-Za-z0-9_.]+) = (\[[^\]]*\])',s);assert m,name
  arr=ast.literal_eval(m.group(2));out += [f'theorem {name} :',f'    (List.ofFn {m.group(1)}).reverse = {fmt(arr[::-1])} := by',f'  rw [{n}.{name}]','  decide +kernel','']
 out += [f'end DiophantineConsistency.Sign17KCoefficientReversed{g:02d}']+[f'#print axioms DiophantineConsistency.Sign17KCoefficientReversed{g:02d}.{name}' for name in names]
 (P/f'Sign17KCoefficientReversed{g:02d}.lean').write_text('\n'.join(out)+'\n')
print('SOURCE_ONLY 17 reversed coefficient list drafts; no Lean or file theorem')
