import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import OAI.Combinatorics.Progressions.Lattices.IntegerAffineResidues
import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

noncomputable def integralRealPolynomialSubring (σ : Type*) : Subring (MvPolynomial σ ℝ) :=
  (MvPolynomial.map (Int.castRingHom ℝ)).range

def realPolynomialCoefficientGrid (q : ℕ) (P : MvPolynomial σ ℝ) : Prop :=
  (fun m => P.coeff m) ∈ realDenominatorGrid q

theorem mem_integralRealPolynomialSubring_iff (P : MvPolynomial σ ℝ) :
    P ∈ integralRealPolynomialSubring σ ↔
      ∀ m, ∃ z : ℤ, (z : ℝ) = P.coeff m := by
  constructor
  · rintro ⟨Q, rfl⟩ m
    exact ⟨Q.coeff m, by simp [coeff_map]⟩
  · intro h
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨m, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
    exact h m

theorem C_int_mem_integralRealPolynomialSubring (z : ℤ) :
    C (z : ℝ) ∈ integralRealPolynomialSubring σ :=
  ⟨C z, by simp⟩

theorem X_mem_integralRealPolynomialSubring (i : σ) :
    (X i : MvPolynomial σ ℝ) ∈ integralRealPolynomialSubring σ :=
  ⟨X i, by simp⟩

theorem rename_mem_integralRealPolynomialSubring {τ : Type*} (f : σ → τ)
    {P : MvPolynomial σ ℝ} (hP : P ∈ integralRealPolynomialSubring σ) :
    rename f P ∈ integralRealPolynomialSubring τ := by
  obtain ⟨Q, rfl⟩ := hP
  exact ⟨rename f Q, MvPolynomial.map_rename _ _ _⟩

theorem realPolynomialCoefficientGrid_iff (q : ℕ) (P : MvPolynomial σ ℝ) :
    realPolynomialCoefficientGrid q P ↔
      C (q : ℝ) * P ∈ integralRealPolynomialSubring σ := by
  rw [mem_integralRealPolynomialSubring_iff]
  simp only [coeff_C_mul]
  constructor
  · rintro ⟨z, hz⟩ m
    exact ⟨z m, congrFun hz m⟩
  · intro h
    choose z hz using h
    exact ⟨z, funext hz⟩

theorem realPolynomialCoefficientGrid_add {q : ℕ} {P Q : MvPolynomial σ ℝ}
    (hP : realPolynomialCoefficientGrid q P) (hQ : realPolynomialCoefficientGrid q Q) :
    realPolynomialCoefficientGrid q (P + Q) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  rw [mul_add]
  exact (integralRealPolynomialSubring σ).add_mem
    ((realPolynomialCoefficientGrid_iff q P).mp hP)
    ((realPolynomialCoefficientGrid_iff q Q).mp hQ)

theorem realPolynomialCoefficientGrid_neg {q : ℕ} {P : MvPolynomial σ ℝ}
    (hP : realPolynomialCoefficientGrid q P) : realPolynomialCoefficientGrid q (-P) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  rw [mul_neg]
  exact (integralRealPolynomialSubring σ).neg_mem
    ((realPolynomialCoefficientGrid_iff q P).mp hP)

theorem realPolynomialCoefficientGrid_X (q : ℕ) (i : σ) :
    realPolynomialCoefficientGrid q (X i) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  exact (integralRealPolynomialSubring σ).mul_mem
    ⟨C (q : ℤ), by simp⟩
    (X_mem_integralRealPolynomialSubring i)

theorem realPolynomialCoefficientGrid_rename {τ : Type*} (f : σ → τ)
    {q : ℕ} {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid q (rename f P) := by
  apply (realPolynomialCoefficientGrid_iff q _).mpr
  simpa using rename_mem_integralRealPolynomialSubring f
    ((realPolynomialCoefficientGrid_iff q P).mp hP)

theorem realPolynomialCoefficientGrid_mono {q r : ℕ} (hqr : q ∣ r)
    {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid r P := by
  obtain ⟨k, rfl⟩ := hqr
  apply (realPolynomialCoefficientGrid_iff (q * k) _).mpr
  have hk : C (k : ℝ) ∈ integralRealPolynomialSubring σ := ⟨C (k : ℤ), by simp⟩
  have h := (integralRealPolynomialSubring σ).mul_mem
    hk
    ((realPolynomialCoefficientGrid_iff q P).mp hP)
  simpa [Nat.cast_mul, map_mul, mul_assoc, mul_left_comm] using h

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U B R : Type*} [CommRing R]

noncomputable def majorShiftCoordinates (e : B → MvPolynomial U R) :
    B → MvPolynomial (U ⊕ B) R :=
  fun b => X (Sum.inr b) + rename Sum.inl (e b)

noncomputable def majorShiftSubstitution (e : B → MvPolynomial U R) :
    U ⊕ B → MvPolynomial (U ⊕ B) R :=
  Sum.elim (fun u => X (Sum.inl u)) (majorShiftCoordinates e)

noncomputable def majorSlowPolynomial (D0 : MvPolynomial B R)
    (E : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (e : B → MvPolynomial U R) : MvPolynomial (U ⊕ B) R :=
  rename Sum.inr D0 + eval₂Hom C (majorShiftSubstitution e) E -
    eval₂Hom C (majorShiftCoordinates e) V

noncomputable def majorRationalPolynomial (Q : MvPolynomial (U ⊕ B) R)
    (V : MvPolynomial B R) (a : B → MvPolynomial U R) :
    MvPolynomial (U ⊕ B) R :=
  Q + eval₂Hom C (majorShiftCoordinates (-a)) V

theorem majorShiftCoordinates_map {T : Type*} [CommRing T]
    (φ : R →+* T) (e : B → MvPolynomial U R) (j : B) :
    map φ (majorShiftCoordinates e j) =
      majorShiftCoordinates (fun i => map φ (e i)) j := by
  simp [majorShiftCoordinates, map_rename]

theorem majorRationalPolynomial_map {T : Type*} [CommRing T]
    (φ : R →+* T) (Q : MvPolynomial (U ⊕ B) R)
    (V : MvPolynomial B R) (a : B → MvPolynomial U R) :
    map φ (majorRationalPolynomial Q V a) =
      majorRationalPolynomial (map φ Q) (map φ V) (fun i => map φ (a i)) := by
  unfold majorRationalPolynomial
  rw [map_add, map_eval₂Hom]
  simp only [coe_eval₂Hom, eval₂_map_comp_C, majorShiftCoordinates_map,
    Pi.neg_apply, map_neg]
  rfl

@[simp] theorem majorShiftCoordinates_eval₂ {T : Type*} [CommRing T]
    (φ : R →+* T) (e : B → MvPolynomial U R)
    (u : U → T) (b : B → T) (j : B) :
    eval₂ φ (Sum.elim u b) (majorShiftCoordinates e j) =
      b j + eval₂ φ u (e j) := by
  simp [majorShiftCoordinates, eval₂_rename, Function.comp_def]

@[simp] theorem majorShiftSubstitution_eval₂ {T : Type*} [CommRing T]
    (φ : R →+* T) (e : B → MvPolynomial U R)
    (u : U → T) (b : B → T) (j : U ⊕ B) :
    eval₂ φ (Sum.elim u b) (majorShiftSubstitution e j) =
      Sum.elim u (fun i => b i + eval₂ φ u (e i)) j := by
  cases j <;> simp [majorShiftSubstitution]

theorem majorSlowPolynomial_eval₂ {T : Type*} [CommRing T]
    (φ : R →+* T) (D0 : MvPolynomial B R)
    (E : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (e : B → MvPolynomial U R) (u : U → T) (b : B → T) :
    eval₂ φ (Sum.elim u b) (majorSlowPolynomial D0 E V e) =
      eval₂ φ b D0 + eval₂ φ (Sum.elim u (fun i => b i + eval₂ φ u (e i))) E -
        eval₂ φ (fun i => b i + eval₂ φ u (e i)) V := by
  simp only [majorSlowPolynomial, eval₂_sub, eval₂_add, eval₂_rename,
    coe_eval₂Hom, ← eval₂_assoc, majorShiftSubstitution_eval₂,
    majorShiftCoordinates_eval₂, Function.comp_def, Sum.elim_inr]

theorem majorRationalPolynomial_eval₂ {T : Type*} [CommRing T]
    (φ : R →+* T) (Q : MvPolynomial (U ⊕ B) R)
    (V : MvPolynomial B R) (a : B → MvPolynomial U R)
    (u : U → T) (b : B → T) :
    eval₂ φ (Sum.elim u b) (majorRationalPolynomial Q V a) =
      eval₂ φ (Sum.elim u b) Q + eval₂ φ (fun i => b i - eval₂ φ u (a i)) V := by
  simp only [majorRationalPolynomial, eval₂_add, coe_eval₂Hom, ← eval₂_assoc,
    majorShiftCoordinates_eval₂, Pi.neg_apply, eval₂_neg, sub_eq_add_neg]

@[simp] theorem majorShiftCoordinates_eval (e : B → MvPolynomial U R)
    (u : U → R) (b : B → R) (j : B) :
    eval (Sum.elim u b) (majorShiftCoordinates e j) = b j + eval u (e j) := by
  simp [majorShiftCoordinates, eval_rename, Function.comp_def]

@[simp] theorem majorShiftSubstitution_eval (e : B → MvPolynomial U R)
    (u : U → R) (b : B → R) (j : U ⊕ B) :
    eval (Sum.elim u b) (majorShiftSubstitution e j) =
      Sum.elim u (fun i => b i + eval u (e i)) j := by
  cases j <;> simp [majorShiftSubstitution]

theorem majorSlowPolynomial_eval (D0 : MvPolynomial B R)
    (E : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (e : B → MvPolynomial U R) (u : U → R) (b : B → R) :
    eval (Sum.elim u b) (majorSlowPolynomial D0 E V e) =
      eval b D0 + eval (Sum.elim u (fun i => b i + eval u (e i))) E -
        eval (fun i => b i + eval u (e i)) V := by
  unfold majorSlowPolynomial
  simp only [map_sub, map_add, eval_rename]
  congr 1
  · congr 1
    change eval (Sum.elim u b) (eval₂ C (majorShiftSubstitution e) E) = _
    rw [← eval_assoc]
    simp only [Function.comp_def, majorShiftSubstitution_eval]
  · change eval (Sum.elim u b) (eval₂ C (majorShiftCoordinates e) V) = _
    rw [← eval_assoc]
    simp only [Function.comp_def, majorShiftCoordinates_eval]

theorem majorRationalPolynomial_eval (Q : MvPolynomial (U ⊕ B) R)
    (V : MvPolynomial B R) (a : B → MvPolynomial U R)
    (u : U → R) (b : B → R) :
    eval (Sum.elim u b) (majorRationalPolynomial Q V a) =
      eval (Sum.elim u b) Q + eval (fun i => b i - eval u (a i)) V := by
  unfold majorRationalPolynomial
  rw [map_add]
  congr 1
  change eval (Sum.elim u b) (eval₂ C (majorShiftCoordinates (-a)) V) = _
  rw [← eval_assoc]
  simp [Function.comp_def, sub_eq_add_neg]

theorem majorShiftCoordinates_mass_le (e : B → MvPolynomial U ℝ)
    {M : ℝ} (he : ∀ i, realPolynomialMass (e i) ≤ M) (j : B) :
    realPolynomialMass (majorShiftCoordinates e j) ≤ 1 + M := by
  apply (realPolynomialMass_add_le _ _).trans
  exact add_le_add (realPolynomialMass_X _).le
    ((realPolynomialMass_rename_le (e j) Sum.inl).trans (he j))

theorem majorShiftSubstitution_mass_le (e : B → MvPolynomial U ℝ)
    {M : ℝ} (hM : 0 ≤ M) (he : ∀ i, realPolynomialMass (e i) ≤ M)
    (j : U ⊕ B) :
    realPolynomialMass (majorShiftSubstitution e j) ≤ 1 + M := by
  cases j with
  | inl i =>
    change realPolynomialMass (X (Sum.inl i) : MvPolynomial (U ⊕ B) ℝ) ≤ _
    rw [realPolynomialMass_X]
    exact le_add_of_nonneg_right hM
  | inr i => exact majorShiftCoordinates_mass_le e he i

theorem majorSlowPolynomial_mass_le (D0 : MvPolynomial B ℝ)
    (E : MvPolynomial (U ⊕ B) ℝ) (V : MvPolynomial B ℝ)
    (e : B → MvPolynomial U ℝ) {M : ℝ} (hM : 0 ≤ M)
    (he : ∀ i, realPolynomialMass (e i) ≤ M) {d : ℕ}
    (hE : E.totalDegree ≤ d) (hV : V.totalDegree ≤ d) :
    realPolynomialMass (majorSlowPolynomial D0 E V e) ≤
      realPolynomialMass D0 +
        (realPolynomialMass E + realPolynomialMass V) * (1 + M) ^ d := by
  have hE' := realPolynomialMass_substitution_le E (majorShiftSubstitution e)
    (show 1 ≤ 1 + M by linarith) (majorShiftSubstitution_mass_le e hM he) hE
  have hV' := realPolynomialMass_substitution_le V (majorShiftCoordinates e)
    (show 1 ≤ 1 + M by linarith) (majorShiftCoordinates_mass_le e he) hV
  unfold majorSlowPolynomial
  exact (realPolynomialMass_sub_le _ _).trans
    (((add_le_add ((realPolynomialMass_add_le _ _).trans
      (add_le_add (realPolynomialMass_rename_le D0 Sum.inr) hE')) hV')).trans
      (by ring_nf; rfl))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {σ J R : Type*} [Fintype J] [CommRing R] [Module R ℝ]

@[simp] theorem coefficients_ofCoordinates_basisFun
    (Q : J → MvPolynomial σ ℝ) (α : σ →₀ ℕ) (j : J) :
    coefficients (ofCoordinates (R := R) (Pi.basisFun ℝ J) Q) α j =
      (Q j).coeff α := by
  have h := congrArg (fun polynomial : MvPolynomial σ ℝ => polynomial.coeff α)
    (coordinate_ofCoordinates (R := R) (Pi.basisFun ℝ J) Q j)
  simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe,
    Module.Basis.coord_apply, Pi.basisFun_repr] using h

theorem coefficients_ofCoordinates_mem_realDenominatorGrid
    (Q : J → MvPolynomial σ ℝ) (q : ℕ)
    (hQ : ∀ j, realPolynomialCoefficientGrid q (Q j)) (α : σ →₀ ℕ) :
    coefficients (ofCoordinates (R := R) (Pi.basisFun ℝ J) Q) α ∈
      realDenominatorGrid q := by
  classical
  choose z hz using hQ
  refine ⟨fun j => z j α, funext fun j => ?_⟩
  change (z j α : ℝ) = (q : ℝ) *
    coefficients (ofCoordinates (R := R) (Pi.basisFun ℝ J) Q) α j
  rw [coefficients_ofCoordinates_basisFun]
  exact congrFun (hz j) α

theorem coefficients_ofCoordinates_slowBound
    (Q : J → MvPolynomial σ ℝ) (T : σ → ℝ) (S : ℝ)
    (hQ : ∀ j α, |(Q j).coeff α| ≤ S / monomialScale T α) :
    ∀ α j, |coefficients (ofCoordinates (R := R) (Pi.basisFun ℝ J) Q) α j| ≤
      S / monomialScale T α := by
  intro α j
  rw [coefficients_ofCoordinates_basisFun]
  exact hQ j α

end Erdos3.VectorPolynomial

end

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators

variable {U B R : Type*} [CommRing R]

theorem polynomial_substitution_totalDegree_le_ring {I J : Type*}
    (P : MvPolynomial I R) (f : I → MvPolynomial J R) {k d : ℕ}
    (hf : ∀ i, (f i).totalDegree ≤ k) (hP : P.totalDegree ≤ d) :
    (eval₂Hom C f P).totalDegree ≤ d * k := by
  classical
  rw [coe_eval₂Hom, eval₂_eq]
  apply totalDegree_finsetSum_le
  intro α hα
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ α.support, (f i ^ α i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ α.support, α i * k := Finset.sum_le_sum (fun i _ =>
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i)))
    _ = (α.sum fun _ n => n) * k := by rw [← Finset.sum_mul]; rfl
    _ ≤ d * k := Nat.mul_le_mul_right _ ((le_totalDegree hα).trans hP)

private theorem variable_totalDegree_le_one {I : Type*} (i : I) :
    (X i : MvPolynomial I R).totalDegree ≤ 1 := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    let := h
    have hz : (X i : MvPolynomial I R) = 0 := Subsingleton.elim _ _
    simp only [hz, totalDegree_zero, Nat.zero_le]
  | inr h =>
    let := h
    simp only [totalDegree_X, le_refl]

 theorem majorShiftCoordinates_totalDegree_le (e : B → MvPolynomial U R)
    {k : ℕ} (he : ∀ j, (e j).totalDegree ≤ k) (j : B) :
    (majorShiftCoordinates e j).totalDegree ≤ max 1 k := by
  apply (totalDegree_add _ _).trans
  exact max_le_max (variable_totalDegree_le_one _) ((totalDegree_rename_le _ _).trans (he j))

 theorem majorShiftSubstitution_totalDegree_le (e : B → MvPolynomial U R)
    {k : ℕ} (he : ∀ j, (e j).totalDegree ≤ k) (j : U ⊕ B) :
    (majorShiftSubstitution e j).totalDegree ≤ max 1 k := by
  cases j with
  | inl i => exact (variable_totalDegree_le_one (Sum.inl i)).trans (le_max_left 1 k)
  | inr j => exact majorShiftCoordinates_totalDegree_le e he j

 theorem majorSlowPolynomial_totalDegree_le
    (D₀ : MvPolynomial B R) (E : MvPolynomial (U ⊕ B) R)
    (V : MvPolynomial B R) (e : B → MvPolynomial U R) {d k : ℕ}
    (hD₀ : D₀.totalDegree ≤ d) (hE : E.totalDegree ≤ d) (hV : V.totalDegree ≤ d)
    (he : ∀ j, (e j).totalDegree ≤ k) :
    (majorSlowPolynomial D₀ E V e).totalDegree ≤ d * max 1 k := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · exact (totalDegree_rename_le _ _).trans (hD₀.trans
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left d (le_max_left 1 k)))
    · exact polynomial_substitution_totalDegree_le_ring E _
        (majorShiftSubstitution_totalDegree_le e he) hE
  · exact polynomial_substitution_totalDegree_le_ring V _
      (majorShiftCoordinates_totalDegree_le e he) hV

 theorem majorRationalPolynomial_totalDegree_le
    (Q : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (a : B → MvPolynomial U R) {d k : ℕ}
    (hQ : Q.totalDegree ≤ d) (hV : V.totalDegree ≤ d)
    (ha : ∀ j, (a j).totalDegree ≤ k) :
    (majorRationalPolynomial Q V a).totalDegree ≤ d * max 1 k := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact hQ.trans
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left d (le_max_left 1 k))
  · exact polynomial_substitution_totalDegree_le_ring V _
      (majorShiftCoordinates_totalDegree_le (-a)
        (fun j => by simpa only [Pi.neg_apply, totalDegree_neg] using ha j)) hV

 theorem majorSlowPolynomial_totalDegree_le_square
    (D₀ : MvPolynomial B R) (E : MvPolynomial (U ⊕ B) R)
    (V : MvPolynomial B R) (e : B → MvPolynomial U R) {d : ℕ}
    (hD₀ : D₀.totalDegree ≤ d) (hE : E.totalDegree ≤ d) (hV : V.totalDegree ≤ d)
    (he : ∀ j, (e j).totalDegree ≤ d) :
    (majorSlowPolynomial D₀ E V e).totalDegree ≤ (d + 1)^2 := by
  apply (majorSlowPolynomial_totalDegree_le D₀ E V e hD₀ hE hV he).trans
  have hmax : max 1 d ≤ d + 1 := max_le (by omega) (by omega)
  calc
    d * max 1 d ≤ d * (d + 1) := Nat.mul_le_mul_left d hmax
    _ ≤ (d + 1)^2 := by nlinarith

 theorem majorRationalPolynomial_totalDegree_le_square
    (Q : MvPolynomial (U ⊕ B) R) (V : MvPolynomial B R)
    (a : B → MvPolynomial U R) {d : ℕ}
    (hQ : Q.totalDegree ≤ d) (hV : V.totalDegree ≤ d)
    (ha : ∀ j, (a j).totalDegree ≤ d) :
    (majorRationalPolynomial Q V a).totalDegree ≤ (d + 1)^2 := by
  apply (majorRationalPolynomial_totalDegree_le Q V a hQ hV ha).trans
  have hmax : max 1 d ≤ d + 1 := max_le (by omega) (by omega)
  calc
    d * max 1 d ≤ d * (d + 1) := Nat.mul_le_mul_left d hmax
    _ ≤ (d + 1)^2 := by nlinarith

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ τ : Type*}

private theorem cleared_substitution_term
    (V : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ)
    (qV qA d : ℕ) (m : σ →₀ ℕ) (hm : m.sum (fun _ n => n) ≤ d) :
    C ((qV * qA ^ d : ℕ) : ℝ) *
        (C (V.coeff m) * ∏ i ∈ m.support, A i ^ m i) =
      C ((qV : ℝ) * V.coeff m) * C ((qA : ℝ) ^ (d - m.sum (fun _ n => n))) *
        ∏ i ∈ m.support, (C (qA : ℝ) * A i) ^ m i := by
  classical
  rw [show (∏ i ∈ m.support, (C (qA : ℝ) * A i) ^ m i) =
      C (qA : ℝ) ^ m.sum (fun _ n => n) * ∏ i ∈ m.support, A i ^ m i by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rfl]
  simp only [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
  calc
    _ = (C (qV : ℝ) * C (V.coeff m)) * C (qA : ℝ) ^ d *
        (∏ i ∈ m.support, A i ^ m i) := by ring
    _ = _ := by
      rw [show C (qA : ℝ) ^ d =
        C (qA : ℝ) ^ (d - m.sum (fun _ n => n)) * C (qA : ℝ) ^ m.sum (fun _ n => n) by
        rw [← pow_add, Nat.sub_add_cancel hm]]
      ring

theorem polynomial_substitution_cleared_mem
    (S : Subring (MvPolynomial τ ℝ))
    (V : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ)
    (qV qA d : ℕ) (hdegree : V.totalDegree ≤ d)
    (hV : ∀ m ∈ V.support, C ((qV : ℝ) * V.coeff m) ∈ S)
    (hA : ∀ i, C (qA : ℝ) * A i ∈ S)
    (hqA : C (qA : ℝ) ∈ S) :
    C ((qV * qA ^ d : ℕ) : ℝ) * aeval A V ∈ S := by
  classical
  rw [aeval_def, eval₂_eq, Finset.mul_sum]
  apply S.sum_mem
  intro m hm
  change C ((qV * qA ^ d : ℕ) : ℝ) *
    (C (V.coeff m) * ∏ i ∈ m.support, A i ^ m i) ∈ S
  rw [cleared_substitution_term V A qV qA d m ((le_totalDegree hm).trans hdegree)]
  apply S.mul_mem
  · apply S.mul_mem (hV m hm)
    simpa only [map_pow] using S.pow_mem hqA (d - m.sum (fun _ n => n))
  · exact S.prod_mem fun i _ => S.pow_mem (hA i) (m i)

theorem realPolynomialCoefficientGrid_substitute
    (V : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ)
    (qV qA d : ℕ) (hdegree : V.totalDegree ≤ d)
    (hV : realPolynomialCoefficientGrid qV V)
    (hA : ∀ i, realPolynomialCoefficientGrid qA (A i)) :
    realPolynomialCoefficientGrid (qV * qA ^ d) (aeval A V) := by
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  apply polynomial_substitution_cleared_mem (integralRealPolynomialSubring τ)
    V A qV qA d hdegree
  · obtain ⟨z, hz⟩ := hV
    intro m _
    have hm : (z m : ℝ) = (qV : ℝ) * V.coeff m := congrFun hz m
    rw [← hm]
    exact C_int_mem_integralRealPolynomialSubring (z m)
  · exact fun i => (realPolynomialCoefficientGrid_iff _ _).mp (hA i)
  · exact ⟨C (qA : ℤ), by simp⟩

theorem realPolynomialCoefficientGrid_substitute_common
    (V : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ)
    (q d : ℕ) (hdegree : V.totalDegree ≤ d)
    (hV : realPolynomialCoefficientGrid q V)
    (hA : ∀ i, realPolynomialCoefficientGrid q (A i)) :
    realPolynomialCoefficientGrid (q ^ (d + 1)) (aeval A V) := by
  simpa only [pow_succ'] using
    realPolynomialCoefficientGrid_substitute V A q q d hdegree hV hA

theorem majorShiftCoordinates_coefficientGrid {U B : Type*}
    (a : B → MvPolynomial U ℝ) (q : ℕ)
    (ha : ∀ b, realPolynomialCoefficientGrid q (a b)) (b : B) :
    realPolynomialCoefficientGrid q (majorShiftCoordinates a b) := by
  exact realPolynomialCoefficientGrid_add (realPolynomialCoefficientGrid_X q _)
    (realPolynomialCoefficientGrid_rename Sum.inl (ha b))

theorem majorRationalPolynomial_coefficientGrid {U B : Type*}
    (Q : MvPolynomial (U ⊕ B) ℝ) (V : MvPolynomial B ℝ)
    (a : B → MvPolynomial U ℝ) (q d : ℕ)
    (hdegree : V.totalDegree ≤ d)
    (hQ : realPolynomialCoefficientGrid q Q)
    (hV : realPolynomialCoefficientGrid q V)
    (ha : ∀ b, realPolynomialCoefficientGrid q (a b)) :
    realPolynomialCoefficientGrid (q ^ (d + 1)) (majorRationalPolynomial Q V a) := by
  apply realPolynomialCoefficientGrid_add
  · exact realPolynomialCoefficientGrid_mono (dvd_pow_self q (by omega)) hQ
  · exact realPolynomialCoefficientGrid_substitute_common V
      (majorShiftCoordinates (-a)) q d hdegree hV
      (majorShiftCoordinates_coefficientGrid (-a) q
        (fun b => realPolynomialCoefficientGrid_neg (ha b)))

theorem realPolynomialCoefficientGrid_ratCast_iff
    (q : ℕ) (P : MvPolynomial σ ℚ) :
    realPolynomialCoefficientGrid q (map (algebraMap ℚ ℝ) P) ↔
      (fun m => P.coeff m) ∈ denominatorGrid q := by
  simp only [realPolynomialCoefficientGrid, coeff_map]
  exact real_cast_mem_denominatorGrid_iff q (fun m => P.coeff m)

theorem majorRationalPolynomial_denominatorGrid {U B : Type*}
    (Q : MvPolynomial (U ⊕ B) ℚ) (V : MvPolynomial B ℚ)
    (a : B → MvPolynomial U ℚ) (q d : ℕ)
    (hdegree : V.totalDegree ≤ d)
    (hQ : (fun m => Q.coeff m) ∈ denominatorGrid q)
    (hV : (fun m => V.coeff m) ∈ denominatorGrid q)
    (ha : ∀ b, (fun m => (a b).coeff m) ∈ denominatorGrid q) :
    (fun m => (majorRationalPolynomial Q V a).coeff m) ∈ denominatorGrid (q ^ (d + 1)) := by
  apply (realPolynomialCoefficientGrid_ratCast_iff _ _).mp
  rw [majorRationalPolynomial_map]
  apply majorRationalPolynomial_coefficientGrid
  · apply le_trans (b := V.totalDegree) ?_ hdegree
    unfold totalDegree
    apply Finset.sup_le
    intro m hm
    exact le_totalDegree (support_map_subset (algebraMap ℚ ℝ) V hm)
  · exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr hQ
  · exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr hV
  · exact fun b => (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr (ha b)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ τ : Type*}

theorem realPolynomialCoefficientGrid_aeval_integral
    (P : MvPolynomial σ ℝ) (A : σ → MvPolynomial τ ℝ) (q : ℕ)
    (hP : realPolynomialCoefficientGrid q P)
    (hA : ∀ i, realPolynomialCoefficientGrid 1 (A i)) :
    realPolynomialCoefficientGrid q (aeval A P) := by
  simpa only [one_pow, mul_one] using
    realPolynomialCoefficientGrid_substitute P A q 1 P.totalDegree le_rfl hP hA

theorem realPolynomialCoefficientGrid_intCast (P : MvPolynomial σ ℤ) :
    realPolynomialCoefficientGrid 1 (map (Int.castRingHom ℝ) P) := by
  apply (realPolynomialCoefficientGrid_iff _ _).mpr
  simpa only [Nat.cast_one, map_one, one_mul] using
    (show map (Int.castRingHom ℝ) P ∈ integralRealPolynomialSubring σ from ⟨P, rfl⟩)

theorem realPolynomialCoefficientGrid_integral_aeval
    {q : ℕ} {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P)
    (A : σ → MvPolynomial τ ℝ)
    (hA : ∀ i, A i ∈ integralRealPolynomialSubring τ) :
    realPolynomialCoefficientGrid q (aeval A P) := by
  have hA' : ∀ i, realPolynomialCoefficientGrid 1 (A i) := by
    intro i
    apply (realPolynomialCoefficientGrid_iff _ _).mpr
    simpa only [Nat.cast_one, map_one, one_mul] using hA i
  exact realPolynomialCoefficientGrid_aeval_integral P A q hP hA'

theorem realPolynomialCoefficientGrid_intCast_aeval
    {q : ℕ} {P : MvPolynomial σ ℝ} (hP : realPolynomialCoefficientGrid q P)
    (A : σ → MvPolynomial τ ℤ) :
    realPolynomialCoefficientGrid q
      (aeval (fun i => map (Int.castRingHom ℝ) (A i)) P) := by
  exact realPolynomialCoefficientGrid_integral_aeval hP _ (fun i => ⟨A i, rfl⟩)

theorem realPolynomialCoefficientGrid_weightedHomogeneousComponent
    {M : Type*} [AddCommMonoid M] (w : σ → M) (d : M)
    (q : ℕ) (P : MvPolynomial σ ℝ) (hP : realPolynomialCoefficientGrid q P) :
    realPolynomialCoefficientGrid q (weightedHomogeneousComponent w d P) := by
  classical
  obtain ⟨z, hz⟩ := hP
  refine ⟨fun m => if Finsupp.weight w m = d then z m else 0, funext (fun m => ?_)⟩
  change ((if Finsupp.weight w m = d then z m else 0 : ℤ) : ℝ) =
    (q : ℝ) * (weightedHomogeneousComponent w d P).coeff m
  by_cases hm : Finsupp.weight w m = d
  · have hzm : (z m : ℝ) = (q : ℝ) * P.coeff m := congrFun hz m
    simpa [coeff_weightedHomogeneousComponent, hm] using hzm
  · simp [coeff_weightedHomogeneousComponent, hm]

end Erdos3

end

section

namespace Erdos3

theorem den_dvd_of_mem_denominatorGrid {ι : Type*} {q : ℕ} (hq : 0 < q)
    {x : ι → ℚ} (hx : x ∈ denominatorGrid q) (i : ι) :
    (x i).den ∣ q := by
  obtain ⟨z, hz⟩ := (mem_denominatorGrid_iff q hq x).mp hx
  rw [hz i]
  have h := Rat.den_dvd (z i) (q : ℤ)
  rw [Rat.divInt_eq_div, Int.cast_natCast] at h
  exact Int.natCast_dvd_natCast.mp h

theorem den_le_of_mem_denominatorGrid {ι : Type*} {q : ℕ} (hq : 0 < q)
    {x : ι → ℚ} (hx : x ∈ denominatorGrid q) (i : ι) :
    (x i).den ≤ q :=
  Nat.le_of_dvd hq (den_dvd_of_mem_denominatorGrid hq hx i)

theorem coeff_den_dvd_of_realPolynomialCoefficientGrid {σ : Type*}
    {q : ℕ} (hq : 0 < q) (P : MvPolynomial σ ℚ)
    (hP : realPolynomialCoefficientGrid q (MvPolynomial.map (algebraMap ℚ ℝ) P))
    (α : σ →₀ ℕ) : (P.coeff α).den ∣ q :=
  den_dvd_of_mem_denominatorGrid hq
    ((realPolynomialCoefficientGrid_ratCast_iff q P).mp hP) α

theorem coeff_den_le_of_realPolynomialCoefficientGrid {σ : Type*}
    {q : ℕ} (hq : 0 < q) (P : MvPolynomial σ ℚ)
    (hP : realPolynomialCoefficientGrid q (MvPolynomial.map (algebraMap ℚ ℝ) P))
    (α : σ →₀ ℕ) : (P.coeff α).den ≤ q :=
  Nat.le_of_dvd hq (coeff_den_dvd_of_realPolynomialCoefficientGrid hq P hP α)

end Erdos3

end

end OAI
