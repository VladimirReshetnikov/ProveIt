#!/usr/bin/env python3
"""Generate source-only staged unions over six audited two-block batches."""
import sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent
for prev,mid,end,left,right in [(224,288,352,'04','05'),(352,416,480,'06','07'),(480,544,608,'08','09'),(608,672,736,'10','11'),(736,800,864,'12','13'),(864,928,942,'14','15')]:
 s=f'''import DiophantineConsistency.Sign17KWeightUnion{prev}
import DiophantineConsistency.Sign17KWeightAggregateBatch{left}
import DiophantineConsistency.Sign17KWeightAggregateBatch{right}

/-! SOURCE-ONLY: append two weight blocks to the prior union. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17KWeightUnion{end}
open WangTiles942

def indices{mid} : Fin {mid} → Fin 942 := Fin.append
  Sign17KWeightUnion{prev}.indices Sign17KWeightAggregateBatch{left}.indices

def weights{mid} : Fin {mid} → ℕ := Fin.append
  Sign17KWeightUnion{prev}.weights Sign17KWeightAggregateBatch{left}.weights

def indices : Fin {end} → Fin 942 := Fin.append indices{mid}
  Sign17KWeightAggregateBatch{right}.indices

def weights : Fin {end} → ℕ := Fin.append weights{mid}
  Sign17KWeightAggregateBatch{right}.weights

theorem all_weights{mid} (i : Fin {mid}) :
    selectorWeight (tile (indices{mid} i)) = weights{mid} i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    Sign17KWeightUnion{prev}.indices Sign17KWeightAggregateBatch{left}.indices
    Sign17KWeightUnion{prev}.weights Sign17KWeightAggregateBatch{left}.weights
    Sign17KWeightUnion{prev}.all_weights Sign17KWeightAggregateBatch{left}.all_weights i

theorem all_weights (i : Fin {end}) :
    selectorWeight (tile (indices i)) = weights i := by
  exact Sign17KWeightAppend.append_certificates
    (fun x => selectorWeight (tile x))
    indices{mid} Sign17KWeightAggregateBatch{right}.indices
    weights{mid} Sign17KWeightAggregateBatch{right}.weights
    all_weights{mid} Sign17KWeightAggregateBatch{right}.all_weights i

end DiophantineConsistency.Sign17KWeightUnion{end}
#print axioms DiophantineConsistency.Sign17KWeightUnion{end}.all_weights{mid}
#print axioms DiophantineConsistency.Sign17KWeightUnion{end}.all_weights
'''
 p=here/f'Sign17KWeightUnion{end}.lean'
 if p.exists(): raise SystemExit('refusing overwrite: '+str(p))
 p.write_text(s)
print('GENERATED_SOURCE_ONLY: six stages through Fin942; no Lean or candidate-rank theorem')
