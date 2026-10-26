import DiophantineConsistency.NativePellBootstrap
import DiophantineConsistency.NativePellScaleBounds
open DiophantineConsistency.NativePellBootstrap
namespace NativeRankRefinement

theorem envelope_implies_forty {q R : ℤ} (hq : 3 ≤ q)
    (hR : (2*q-1)*(q^2-1) ≤ R) : 40 ≤ R := by
  have hq2 : (8 : ℤ) ≤ q^2-1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hq2 (show 0 ≤ 2*q-1 by omega)
  nlinarith

theorem envelope_arithmetic_sharp : (2*(3:ℤ)-1)*(3^2-1)=40 := by norm_num

#print axioms source_native_rank_envelope
#print axioms source_native_rank_ge_twentyfour
#print axioms DiophantineConsistency.NativePellScaleBounds.source_rank_gt_three_q
#print axioms envelope_implies_forty
end NativeRankRefinement
