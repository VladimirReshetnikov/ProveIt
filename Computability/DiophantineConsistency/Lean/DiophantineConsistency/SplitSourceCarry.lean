import DiophantineConsistency.SplitCarry
import DiophantineConsistency.SplitSourceBounds

/-! # The generic split116 coefficient carry contract -/

namespace DiophantineConsistency.SplitSourceCarry

open Polynomial Finset Jones1982
open scoped BigOperators

/-- All degree and coefficient side conditions of the generic two-block
contract follow from the split116 kernel bounds. Word positivity and the low
range are explicit; no source residual interpretation is supplied. -/
theorem tau_product_iff {B b g k t : ℕ} (w : Fin 31 → ℕ)
    (hwinj : Function.Injective w) (hw : ∀ i,w i≤116)
    (hb : b=2^k) (hB : B=2^t) (ht : 2≤t) (hbB : b≤B) (hg : g<B^117)
    (targets : Finset ℕ) (hTargets : ∀ i∈targets,i<2162)
    (D0 D1 D2 : ℤ[X]) {H : ℤ} (hH : 0<H)
    (hk : SplitWordBounds.KernelBounds D0 D1 D2 H)
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
    exact SplitSourceBounds.product_natDegree_lt_2162 w hw (fun i => (z i:ℤ)+1) D0 D1 D2 hk
  · exact hJ

/-- An indexed array of target positions gives the corresponding pointwise
coefficient statement. Injectivity is needed by mask-population calibration,
but is unnecessary for this logical conversion. -/
theorem tau_targets_iff {r B b g k t : ℕ} (w : Fin 31 → ℕ)
    (hwinj : Function.Injective w) (hw : ∀ i,w i≤116)
    (hb : b=2^k) (hB : B=2^t) (ht : 2≤t) (hbB : b≤B) (hg : g<B^117)
    (q : Fin r → ℕ) (hq : ∀ j,q j<2162)
    (D0 D1 D2 : ℤ[X]) {H : ℤ} (hH : 0<H)
    (hk : SplitWordBounds.KernelBounds D0 D1 D2 H)
    (hbase : 4096*H*(b:ℤ)^2≤(2:ℤ)^t)
    (hJ : 0≤SplitCarry.highInt B g w D0 D1 D2 (univ.image q)) :
    τ 2 (SplitCarry.word B 117 g (SplitCarry.highInt B g w D0 D1 D2 (univ.image q)))
      (SplitCarry.packedMask B b 117 w (univ.image q))=0 ↔
      ∃ z : Fin 31 → ℕ,(∀ i,z i<b) ∧ g=LowMaskCoding.indexedCode B w z ∧
        ∀ j,(SplitCoefficientBounds.product w (fun i => (z i:ℤ)+1) D0 D1 D2).coeff (q j)=0 := by
  have htargets : ∀ i∈univ.image q,i<2162 := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := mem_image.mp hi
    exact hq j
  rw [tau_product_iff w hwinj hw hb hB ht hbB hg (univ.image q) htargets D0 D1 D2 hH hk hbase hJ]
  constructor
  · rintro ⟨z,hz,hcode,hcoeff⟩
    exact ⟨z,hz,hcode,fun j => hcoeff (q j) (mem_image.mpr ⟨j,mem_univ j,rfl⟩)⟩
  · rintro ⟨z,hz,hcode,hcoeff⟩
    refine ⟨z,hz,hcode,?_⟩
    intro i hi
    obtain ⟨j,_,rfl⟩ := mem_image.mp hi
    exact hcoeff j

end DiophantineConsistency.SplitSourceCarry
