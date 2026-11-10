#!/usr/bin/env python3
"""Generate finite control coefficient proposal; external cross-check only."""
from pathlib import Path
import hashlib,json,sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;p=here.parent/'padding-staircase-independent/coefficients.json';raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()=='43f31dd15eb258cca8979aaf39ea8987df9ac573246e50f94bd43769c470dc93';external=json.loads(raw)
cs=[0]*44
for start,n,bit in [(942,9,35),(960,9,18),(969,8,27),(978,8,10)]:
 for j in range(n):cs[start+j-942]+=2*2**(bit+j)
assert cs==external[942:986]
values=', '.join(map(str,cs))
s=f'''import DiophantineConsistency.Sign17KRankedRawWord

/-! SOURCE-ONLY: combine 34 control terms into a finite coefficient vector. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KControlCoefficients
open CurrentKernel2011
open scoped BigOperators

def coefficients : Fin 44 → ℕ := ![{values}]

theorem controls_as_sum (r : ℕ) :
    Sign17KRankedRawWord.controls r =
      ∑ i : Fin 44, coefficients i * r ^ (1005 - (942 + i.val)) := by
  simp [Sign17KRankedRawWord.controls, coefficients, Fin.sum_univ_succ] <;> ring

theorem rawWord_control_coefficients (r : ℕ) :
    rawWord r = r ^ 18 + r ^ 1004 + r ^ 2020 +
      (∑ i : Fin 942, 2 * Sign17KWeightUnion942.weights i * r ^ (1005 - i.val)) +
      (∑ i : Fin 44, coefficients i * r ^ (1005 - (942 + i.val))) := by
  rw [Sign17KRankedRawWord.rawWord_ranked, controls_as_sum]

end DiophantineConsistency.Sign17KControlCoefficients
#print axioms DiophantineConsistency.Sign17KControlCoefficients.controls_as_sum
#print axioms DiophantineConsistency.Sign17KControlCoefficients.rawWord_control_coefficients
'''
out=here/'Sign17KControlCoefficients.lean'
if out.exists():raise SystemExit('refusing overwrite')
out.write_text(s);print('GENERATED_SOURCE_ONLY; 44 coefficients cross-checked externally; no Lean/file theorem')
