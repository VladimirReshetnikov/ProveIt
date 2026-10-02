"""Reproduce every literal seed/interval rank through length eight for the gate."""
from pathlib import Path
import sys,json
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent))
from audit_literal import literal
A,B,I,F=1026,56481,1,2
out={'matrices':[A,B],'initial':I,'final':F,'slices':[]}
for N in range(1,9):
    rank,number,witness=literal(4,A,B,I,F,N)
    assert rank==min(N,7)
    out['slices'].append({'length':N,'maximum_rank':rank,'hull_targets':number,'witness':witness})
out['passed']=True
assert out==json.loads((ROOT/'literal_rank_seven.json').read_text())
print('Literal four-state receipt reproduced: 509 hull targets, maxima 1 2 3 4 5 6 7 7')
