#!/usr/bin/env python3
"""Generate source-only tile coefficient vectors with external cross-check."""
from pathlib import Path
import hashlib,json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;cp=here.parent/'padding-staircase-independent/coefficients.json';wp=here.parent/'nine-sharing-sign17-k-ranking-witness/witness.json';cb=cp.read_bytes();wb=wp.read_bytes();assert hashlib.sha256(cb).hexdigest()=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93';assert hashlib.sha256(wb).hexdigest()=='7f50654d30197158157533857892ddde91b7234bfdfe0cc6089282e5613b81a3';c=json.loads(cb);w=json.loads(wb)['rows'];assert len(w)==942 and c[:942]==[2*x['weight'] for x in w]
for n in range(16):
 lo,hi=(0,32) if n==0 else (32+64*(n-1),min(32+64*n,942));count=hi-lo;assert count>0
 mod='Sign17KWeightAggregateProbe' if n==0 else f'Sign17KWeightAggregateBatch{n:02d}'
 name=f'Sign17KTileCoefficients{n:02d}';values=', '.join(map(str,c[lo:hi]))
 s=f'''import DiophantineConsistency.{mod}

/-! SOURCE-ONLY: doubled in-Lean weights versus this finite literal block. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.{name}

def literal : Fin {count} → ℕ := ![{values}]

theorem doubled_weights (i : Fin {count}) :
    2 * {mod}.weights i = literal i := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.{name}
#print axioms DiophantineConsistency.{name}.doubled_weights
'''
 p=here/(name+'.lean')
 if p.exists():raise SystemExit('refusing overwrite '+str(p))
 p.write_text(s)
print('GENERATED_SOURCE_ONLY: 16 blocks cover 942 externally cross-checked tile coefficients; no Lean or file theorem')
