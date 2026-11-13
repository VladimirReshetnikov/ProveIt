#!/usr/bin/env python3
"""Generate a source-only uniformly quantified 64-row K weight batch."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;w=here.parent/'nine-sharing-sign17-k-ranking-witness/witness.json';raw=w.read_bytes();sha=lambda b:hashlib.sha256(b).hexdigest();assert sha(raw)=='7f50654d30197158157533857892ddde91b7234bfdfe0cc6089282e5613b81a3';rows=json.loads(raw)['rows'][928:942];assert [x['physical'] for x in rows]==list(range(928,942));indices=', '.join(str(x['index']) for x in rows);weights=', '.join(str(x['weight']) for x in rows)
s=f'''import DiophantineConsistency.Sign17ExactDegree

/-! SOURCE-ONLY: one uniformly quantified K weight batch, not a rank theorem. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KWeightAggregateBatch15
open WangTiles942

def indices : Fin 14 → Fin 942 := ![{indices}]
def weights : Fin 14 → ℕ := ![{weights}]

theorem all_weights (i : Fin 14) : selectorWeight (tile (indices i)) = weights i := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.Sign17KWeightAggregateBatch15
#print axioms DiophantineConsistency.Sign17KWeightAggregateBatch15.all_weights
'''
out=here/'Sign17KWeightAggregateBatch15.lean'
if out.exists():raise SystemExit('refusing overwrite')
out.write_text(s);print(json.dumps({'status':'GENERATED_SOURCE_ONLY','rows':14,'source_sha256':sha(s.encode()),'scope':'Uncompiled aggregate weight theorem, no rank or K/file claim.'},sort_keys=True,indent=2))
