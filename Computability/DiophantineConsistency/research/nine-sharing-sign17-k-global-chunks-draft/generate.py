#!/usr/bin/env python3
"""Generate bounded source-only global candidate-tail and adjacency chunks."""
from pathlib import Path
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent
for chunk in range(15):
 off=chunk*64;nz=min(64,941-off);adj=min(64,940-off);nztail=941-off-nz;adjtail=940-off-adj
 assert nz>0 and adj>0 and nztail>=0 and adjtail>=0
 name=f'Sign17KGlobalChunk{chunk:02d}'
 start='theorem start_index : Sign17KWeightUnion942.indices 0 = 0 := by decide +kernel\n\n' if chunk==0 else ''
 report=f'#print axioms DiophantineConsistency.{name}.start_index\n' if chunk==0 else ''
 s=f'''import DiophantineConsistency.Sign17KWeightUnion942

/-! SOURCE-ONLY: global candidate cases at offset {off}. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.{name}

def nonzeroIndex (i : Fin {nz}) : Fin 941 := (Fin.natAdd {off} i).castAdd {nztail}

def adjacentIndex (i : Fin {adj}) : Fin 940 := (Fin.natAdd {off} i).castAdd {adjtail}

{start}theorem nonzero (i : Fin {nz}) :
    Sign17KWeightUnion942.indices (nonzeroIndex i).succ ≠ 0 := by
  fin_cases i <;> decide +kernel

theorem adjacent (i : Fin {adj}) :
    Sign17KWeightUnion942.weights (adjacentIndex i).succ.succ <
      Sign17KWeightUnion942.weights (adjacentIndex i).castSucc.succ := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.{name}
{report}#print axioms DiophantineConsistency.{name}.nonzero
#print axioms DiophantineConsistency.{name}.adjacent
'''
 p=here/(name+'.lean')
 if p.exists():raise SystemExit('refusing overwrite '+str(p))
 p.write_text(s)
print('GENERATED_SOURCE_ONLY: 15 chunks cover 941 tail positions and 940 neighboring pairs; no Lean result')
