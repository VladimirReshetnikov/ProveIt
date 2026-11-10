#!/usr/bin/env python3
"""Generate source-only Fin.addCases assembly for all audited-shape chunks."""
from pathlib import Path
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent
lines=['import DiophantineConsistency.Sign17KGlobalRankConditional']+[f'import DiophantineConsistency.Sign17KGlobalChunk{i:02d}' for i in range(15)]+['','/-! SOURCE-ONLY: proposed chunk-to-global facts and candidate ranks. -/','set_option autoImplicit false','set_option maxRecDepth 10000','set_option maxHeartbeats 4000000','noncomputable section','namespace DiophantineConsistency.Sign17KGlobalAssembly','']
def emit(goal,total,field,theorem):
 lines.extend([goal,'  intro i'])
 depth=1
 for k in range(14):
  remaining=total-64*(k+1);x='i' if k==0 else f'j{k-1}'
  lines.append('  '*depth+f'refine Fin.addCases (m := 64) (n := {remaining}) ?_ ?_ {x}')
  lines.append('  '*depth+'· '+f'intro x{k}')
  lines.append('  '*(depth+1)+f'simpa only [Sign17KGlobalChunk{k:02d}.{field}, Fin.natAdd, Fin.castAdd, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk{k:02d}.{theorem} x{k}')
  lines.append('  '*depth+'· '+f'intro j{k}');depth+=1
 lines.append('  '*depth+f'simpa only [Sign17KGlobalChunk14.{field}, Fin.natAdd, Fin.castAdd, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk14.{theorem} j13')
 lines.append('')
emit('theorem tail_nonzero : ∀ i : Fin 941, Sign17KWeightUnion942.indices i.succ ≠ 0 := by',941,'nonzeroIndex','nonzero')
emit('theorem numeric_adjacent : ∀ i : Fin 940, Sign17KWeightUnion942.weights i.succ.succ < Sign17KWeightUnion942.weights i.castSucc.succ := by',940,'adjacentIndex','adjacent')
lines+=['theorem global_nonzero : ∀ i, i ≠ 0 → Sign17KWeightUnion942.indices i ≠ 0 := by','  intro i hi','  cases i using Fin.cases with','  | zero => exact False.elim (hi rfl)','  | succ i => exact tail_nonzero i','','theorem candidate_positions : ∀ i, MF.WangTiles942.physicalMap (Sign17KWeightUnion942.indices i) = i := by','  exact Sign17KGlobalRankConditional.candidate_positions_if','    Sign17KGlobalChunk00.start_index global_nonzero numeric_adjacent','','end DiophantineConsistency.Sign17KGlobalAssembly','#print axioms DiophantineConsistency.Sign17KGlobalAssembly.tail_nonzero','#print axioms DiophantineConsistency.Sign17KGlobalAssembly.numeric_adjacent','#print axioms DiophantineConsistency.Sign17KGlobalAssembly.global_nonzero','#print axioms DiophantineConsistency.Sign17KGlobalAssembly.candidate_positions']
p=here/'Sign17KGlobalAssembly.lean'
if p.exists():raise SystemExit('refusing overwrite '+str(p))
p.write_text('\n'.join(lines)+'\n');print('GENERATED_SOURCE_ONLY: proposed global Fin941/Fin940 assembly and physical rank')
