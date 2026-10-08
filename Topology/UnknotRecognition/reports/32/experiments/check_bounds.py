"""Exact rational audit of the cutoff used for a safe external-model constant."""
from fractions import Fraction as Q
from pathlib import Path
import json
rows=[(Q(-1,2),Q(1,2),Q(-1,4),Q(3)),
      (Q(3),Q(-3,2),Q(1),Q(9,2)),
      (Q(-9,4),Q(1),Q(-3,4),Q(9,4))]
sums=tuple(sum(row[j] for row in rows) for j in range(4))
assert sums==(Q(1,4),Q(0),Q(0),Q(39,4))
result={'rows':[[str(x) for x in r] for r in rows],
        'sum':[str(x) for x in sums],'strict_cutoff':'m < 39',
        'safe_C':str(3**114),'safe_A':str(32*3**114),
        'scope':'Arithmetic identity only; not a verification of the external Morse model.'}
root=Path(__file__).resolve().parents[1]
(root/'results'/'cutoff_check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
