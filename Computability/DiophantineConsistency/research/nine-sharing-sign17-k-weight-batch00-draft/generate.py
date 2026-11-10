#!/usr/bin/env python3
"""Generate uncompiled K candidate weight theorems for physical rows 0..31."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;w=here.parent/'nine-sharing-sign17-k-ranking-witness/witness.json';raw=w.read_bytes();sha=lambda b:hashlib.sha256(b).hexdigest();assert sha(raw)=='7f50654d30197158157533857892ddde91b7234bfdfe0cc6089282e5613b81a3';rows=json.loads(raw)['rows'];assert len(rows)==942
s='''import DiophantineConsistency.Sign17ExactDegree

/-! SOURCE-ONLY: K candidate tile weights; rank and file binding are separate. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KWeightBatch00
open WangTiles942
'''
for p in range(32):
 row=rows[p];assert row['physical']==p
 s+=f'''\ntheorem weight_{p:03} : selectorWeight (tile ({row['index']} : Fin 942)) = {row['weight']} := by
  decide +kernel
'''
s+='\nend DiophantineConsistency.Sign17KWeightBatch00\n'
for p in range(32):s+=f'#print axioms DiophantineConsistency.Sign17KWeightBatch00.weight_{p:03}\n'
out=here/'Sign17KWeightBatch00.lean'
if out.exists():raise SystemExit('refusing overwrite')
out.write_text(s)
print(json.dumps({'status':'GENERATED_SOURCE_ONLY','physical_first':0,'physical_last':31,
 'source_sha256':sha(s.encode()),'scope':'Uncompiled individual tile weights, not rank or K equality.'},indent=2,sort_keys=True))
