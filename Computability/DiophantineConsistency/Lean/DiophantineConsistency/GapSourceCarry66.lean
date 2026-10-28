import DiophantineConsistency.SplitCarry
import DiophantineConsistency.SplitSourceBounds
import DiophantineConsistency.GapWordBounds66

/-! # The H2082 coefficient carry contract -/

namespace DiophantineConsistency.GapSourceCarry66
set_option maxHeartbeats 1000000

open Polynomial Finset Jones1982
open scoped BigOperators

/-- The inclusive H2082 source degree gives exactly2083 decoder positions. -/
theorem product_natDegree_lt_2083 {m : ℕ} (w : Fin (m+1) → ℕ)
    (hw : ∀ i,w i≤116) (y : Fin (m+1) → ℤ) (D0 D1 D2 : ℤ[X]) {H : ℤ}
    (hk : GapWordBounds66.KernelBounds D0 D1 D2 H) :
    (SplitCoefficientBounds.product w y D0 D1 D2).natDegree<2083 := by
  have h := SplitSourceBounds.product_natDegree_le w hw y D0 D1 D2
    hk.degree_zero hk.degree_one hk.degree_two
  exact lt_of_le_of_lt h (by decide)

/-- All degree and coefficient side conditions of the generic two-block
contract follow from the split116 kernel bounds. Word positivity and the low
range are explicit; no source residual interpretation is supplied. -/
theorem tau_product_iff {B b g k t : ℕ} (w : Fin 31 → ℕ)
    (hwinj : Function.Injective w) (hw : ∀ i,w i≤116)
    (hb : b=2^k) (hB : B=2^t) (ht : 2≤t) (hbB : b≤B) (hg : g<B^117)
    (targets : Finset ℕ) (hTargets : ∀ i∈targets,i<2083)
    (D0 D1 D2 : ℤ[X]) {H : ℤ} (hH : 0<H)
    (hk : GapWordBounds66.KernelBounds D0 D1 D2 H)
    (hbase : 4096*H*(b:ℤ)^2≤(2:ℤ)^t)
    (hJ : 0≤SplitCarry.highInt B g w D0 D1 D2 targets) :
    τ 2 (SplitCarry.word B 117 g (SplitCarry.highInt B g w D0 D1 D2 targets))
      (SplitCarry.packedMask B b 117 w targets)=0 ↔
      ∃ z : Fin 31 → ℕ,(∀ i,z i<b) ∧ g=LowMaskCoding.indexedCode B w z ∧
        ∀ i∈targets,(SplitCoefficientBounds.product w (fun i => (z i:ℤ)+1) D0 D1 D2).coeff i=0 := by
  apply SplitCarry.tau_product_iff_31 w hwinj (fun i => by have h:=hw i; omega)
    hb hB ht hbB hg targets hTargets D0 D1 D2 hH
    hk.coeff_zero hk.coeff_one hk.coeff_two hbase
  · intro z _
    exact product_natDegree_lt_2083 w hw (fun i => (z i:ℤ)+1) D0 D1 D2 hk
  · exact hJ

/-- An indexed array of target positions gives the corresponding pointwise
coefficient statement. Injectivity is needed by mask-population calibration,
but is unnecessary for this logical conversion. -/
theorem tau_targets_iff {r B b g k t : ℕ} (w : Fin 31 → ℕ)
    (hwinj : Function.Injective w) (hw : ∀ i,w i≤116)
    (hb : b=2^k) (hB : B=2^t) (ht : 2≤t) (hbB : b≤B) (hg : g<B^117)
    (q : Fin r → ℕ) (hq : ∀ j,q j<2083)
    (D0 D1 D2 : ℤ[X]) {H : ℤ} (hH : 0<H)
    (hk : GapWordBounds66.KernelBounds D0 D1 D2 H)
    (hbase : 4096*H*(b:ℤ)^2≤(2:ℤ)^t)
    (hJ : 0≤SplitCarry.highInt B g w D0 D1 D2 (univ.image q)) :
    τ 2 (SplitCarry.word B 117 g (SplitCarry.highInt B g w D0 D1 D2 (univ.image q)))
      (SplitCarry.packedMask B b 117 w (univ.image q))=0 ↔
      ∃ z : Fin 31 → ℕ,(∀ i,z i<b) ∧ g=LowMaskCoding.indexedCode B w z ∧
        ∀ j,(SplitCoefficientBounds.product w (fun i => (z i:ℤ)+1) D0 D1 D2).coeff (q j)=0 := by
  have htargets : ∀ i∈univ.image q,i<2083 := by
    simpa only [forall_mem_image, mem_univ, true_implies] using hq
  rw [tau_product_iff w hwinj hw hb hB ht hbB hg (univ.image q) htargets D0 D1 D2 hH hk hbase hJ]
  simp only [forall_mem_image, mem_univ, true_implies]

end DiophantineConsistency.GapSourceCarry66
