import OAI.Combinatorics.Progressions.Linear.MarkedProjectionBounds
import OAI.Combinatorics.Progressions.Polynomial.MarkedPolynomialFunctionalBounds

namespace OAI

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s r : ℕ} (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hH hc hgen in
theorem markedShiftPolynomialGenerator_quotient_height (hω : ∀ i, ω i ≤ s) (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s))
    {q Q : ℕ} (f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t))
    (hf : ∀ i j, RationalHeightLE
      (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q)
    (d k l : ℕ) (p : finiteMarkedPolynomialValues (σ := Fin t) v w marked s d k l)
    (j : Fin q) :
    let T := lieTreeHeight (Fintype.card ι) H s
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let n := finrank ℚ (markedShiftSubalgebra F v w marked t)
    let C := (a + 1) * (rationalSolveHeight n T * T) ^ a
    RationalHeightLE
      (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t)
        (markedShiftPolynomialGenerator F v w marked hw hv t d k l p)) j)
      ((n + 1) * (C * Q) ^ n) := by
  classical
  dsimp only
  let _ : Fintype (NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω) :=
    NilpotentLieFiltration.adaptedBasisIndexFintype (fun _ : Fin t => 1) ω s (by simp) hω
  let g := markedShiftPolynomialGenerator F v w marked hw hv t d k l p
  have hg (i) := markedShiftPolynomialGenerator_coordinate_height F v w marked hw hv
    b ω hF hH hc hgen t d k l p i
  have hcoords (i) := embedding_basis_coordinate_height e
    (F.associatedDegree.polynomialShiftBasis b ω hF t)
    (markedShiftSubalgebra F v w marked t).incl.toLinearMap
    (fun _ _ h => Subtype.ext h) (hH.trans (lieTreeHeight_ge_input _ _ _))
    (fun j i => he i j) g hg i
  have h := linearMap_coordinate_height e f
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
    (fun i j => hf j i) g hcoords j
  simpa only [LieHom.coe_toLinearMap, g, Fintype.card_fin,
    ← finrank_eq_card_basis (F.associatedDegree.polynomialShiftBasis b ω hF t)] using h

include hw hv hH hc hgen in
theorem exists_markedShift_bounded_quotient_frequency (hω : ∀ i, ω i ≤ s) (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s))
    {q Q K A : ℕ} (f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t))
    (hQ : 1 ≤ Q)
    (hf : ∀ i j, RationalHeightLE
      (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q)
    (η : L →ₗ[ℚ] ℚ) (hη : ∀ i, RationalHeightLE (η (b i)) K)
    (a : Fin t → ℚ) (hA : 1 ≤ A) (ha : ∀ i, RationalHeightLE (a i) A)
    (d k l : ℕ)
    (hann : markedShiftPolynomialSubmodule F v w marked t d k l ⊓
      (markedShiftSecondIdeal F v w marked t).toSubmodule ≤
        (η.comp (markedShiftEval F v w marked t a)).ker) :
    let T := lieTreeHeight (Fintype.card ι) H s
    let z := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let n := finrank ℚ (markedShiftSubalgebra F v w marked t)
    let C := (z + 1) * (rationalSolveHeight n T * T) ^ z
    let E := (n + 1) * (C * Q) ^ n
    let V := A ^ s * ((Fintype.card ι + 1) * (T * K) ^ Fintype.card ι)
    let m := finrank ℚ ((markedShiftPolynomialSubmodule F v w marked t d k l).map
      (markedShiftSecondIdeal F v w marked t).toSubmodule.mkQ)
    ∃ ξ : MarkedShiftQuotient F v w marked t →ₗ[ℚ] ℚ,
      (∀ x ∈ markedShiftPolynomialSubmodule F v w marked t d k l,
        ξ (lieQuotientMap (markedShiftSecondIdeal F v w marked t) x) =
          η (markedShiftEval F v w marked t a x)) ∧
      ∀ i, RationalHeightLE (ξ (f i)) ((m + 1) * (rationalSolveHeight m E * V) ^ m) := by
  dsimp only
  have hT : 0 < lieTreeHeight (Fintype.card ι) H s :=
    Nat.zero_lt_of_lt (hH.trans (lieTreeHeight_ge_input _ _ _))
  have hsolve := rationalSolveHeight_pos
    (finrank ℚ (markedShiftSubalgebra F v w marked t)) (Nat.succ_le_iff.mpr hT)
  have hQpos : 0 < Q := Nat.zero_lt_of_lt hQ
  apply exists_bounded_quotient_functional
    (markedShiftPolynomialSubmodule F v w marked t d k l)
    (markedShiftSecondIdeal F v w marked t).toSubmodule f
    (markedShiftPolynomialGenerator F v w marked hw hv t d k l)
    (markedShiftPolynomialGenerator_span F v w marked hw hv t d k l)
    (η.comp (markedShiftEval F v w marked t a)) hann
  · exact Nat.succ_le_iff.mpr (by positivity)
  · intro p j
    exact markedShiftPolynomialGenerator_quotient_height F b ω hF v w marked hw hv
      hH hc hgen hω t e he f hf d k l p j
  · intro p
    exact finiteMarkedPolynomialValues_functional_height v w marked b η hA hc hgen hη
      t d k l a ha p.property

end Erdos3

end

end OAI
