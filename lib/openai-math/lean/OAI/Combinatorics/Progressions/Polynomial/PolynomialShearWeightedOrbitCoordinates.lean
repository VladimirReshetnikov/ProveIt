import OAI.Combinatorics.Progressions.Polynomial.PolynomialDerivationIntertwine
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbit

namespace OAI

section

namespace Erdos3

open MvPolynomial Module VectorPolynomial
open scoped TensorProduct

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}
variable (s : ℕ) (hw : ∀ i, w i ≤ s)

theorem polynomialShearReal_adapted_iff_coordinate_support
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)) :
    (polynomialShearFiltration w s hw).realification.Adapted (fun _ : σ => 1) p ↔
      ∀ a : PolynomialShearIndex w,
        VectorPolynomial.coordinate
          (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p ∈
          weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a) := by
  rw [NilpotentLieFiltration.adapted_iff_coefficients]
  constructor
  · intro hp a α hα
    change α ∈ (VectorPolynomial.coordinate
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p).support at hα
    by_contra hdeg
    have hc := ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
      (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
      (fun j => polynomialShearLayer_span w j) _ _).mp (hp α) a hdeg
    apply (MvPolynomial.mem_support_iff.mp hα)
    rw [VectorPolynomial.coeff_coordinate]
    exact hc
  · intro hp α
    apply ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
      (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
      (fun j => polynomialShearLayer_span w j) _ _).mpr
    intro a ha
    change (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a)
      (VectorPolynomial.coefficients p α) = 0
    have hc : (VectorPolynomial.coordinate
        (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p).coeff α = 0 := by
      by_contra hne
      exact ha (hp a (MvPolynomial.mem_support_iff.mpr hne))
    exact (VectorPolynomial.coeff_coordinate _ p α).symm.trans hc

noncomputable def polynomialShearOrbitParameterCoordinates
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1))
    (a : PolynomialShearIndex w) : MvPolynomial σ ℝ :=
  VectorPolynomial.coordinate
    (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom g.log

theorem polynomialShearOrbitParameterCoordinates_degree
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1))
    (a : PolynomialShearIndex w) :
    polynomialShearOrbitParameterCoordinates s hw g a ∈
      weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a) :=
  (polynomialShearReal_adapted_iff_coordinate_support s hw g.log).mp g.adapted a

theorem polynomialShearOrbitParameterCoordinates_eval
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1))
    (t : σ → ℝ) (a : PolynomialShearIndex w) :
    MvPolynomial.eval t (polynomialShearOrbitParameterCoordinates s hw g a) =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr
        ((polynomialShearFiltration w s hw).realification.polynomialOrbitRealEval
          (fun _ : σ => 1) t g).coord a := by
  exact (VectorPolynomial.coordinate_eval₂
    (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a) t g.log).symm

theorem polynomialShearOrbitParameterCoordinates_reconstruct
    [Fintype (PolynomialShearIndex w)]
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1)) :
    VectorPolynomial.ofCoordinates ((polynomialShearBasis (R := ℚ) w).baseChange ℝ)
      (polynomialShearOrbitParameterCoordinates s hw g) = g.log :=
  VectorPolynomial.ofCoordinates_coordinate _ _

end Erdos3

end

section

namespace Erdos3

open MvPolynomial Module
open scoped BigOperators TensorProduct

variable {σ : Type*} {d : ℕ}

theorem patchParameterSpecialization_rename_parameter (t : σ → ℝ)
    (P : MvPolynomial σ ℝ) :
    patchParameterSpecialization (d := d) t (rename Sum.inl P) = C (MvPolynomial.eval t P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [patchParameterSpecialization]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, rename_X, hP, eval_X]
    simp [patchParameterSpecialization]

theorem patchParameterSpecialization_rename_slot (t : σ → ℝ)
    (P : MvPolynomial (Fin d) ℝ) :
    patchParameterSpecialization t (rename Sum.inr P) = P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [patchParameterSpecialization]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, rename_X, hP, patchParameterSpecialization_X_slot]

variable (w : Fin d → ℕ) [Fintype (PolynomialShearIndex w)]

omit [Fintype (PolynomialShearIndex w)] in

theorem polynomialSymbolicShearTerm_specialization
    (c : PolynomialShearIndex w → MvPolynomial σ ℝ) (t : σ → ℝ)
    (a : PolynomialShearIndex w) :
    patchParameterSpecialization t (polynomialSymbolicShearTerm w c a) =
      C (MvPolynomial.eval t (c a)) * monomial a.2.val 1 := by
  rw [polynomialSymbolicShearTerm, map_mul, patchParameterSpecialization_rename_parameter,
    patchParameterSpecialization_rename_slot]

theorem polynomialSymbolicShearSlot_specialization
    (c : PolynomialShearIndex w → MvPolynomial σ ℝ) (t : σ → ℝ) (i : Fin d) :
    patchParameterSpecialization t (polynomialSymbolicShearSlot w c i) =
      ∑ a : PolynomialShearIndex w,
        if a.1 = i then C (MvPolynomial.eval t (c a)) * monomial a.2.val 1 else 0 := by
  classical
  simp only [polynomialSymbolicShearSlot, map_sum, apply_ite,
    polynomialSymbolicShearTerm_specialization, map_zero]

variable (s : ℕ) (hw : ∀ i, w i ≤ s)
variable (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1))
variable (t : σ → ℝ)

local notation "orbitD" => polynomialShearRealificationEquiv w
  (NilpotentLieBCHGroup.coord
    (NilpotentLieFiltration.polynomialOrbitRealEval
      (NilpotentLieFiltration.realification (polynomialShearFiltration w s hw))
      (fun _ : σ => 1) t g))
local notation "symbolicD" => polynomialSymbolicShearDerivation w
  (polynomialShearOrbitParameterCoordinates s hw g)

theorem polynomialShearOrbitSymbolicDerivation_X_slot_specialization (i : Fin d) :
    patchParameterSpecialization t ((symbolicD).val (X (Sum.inr i))) = (orbitD).val (X i) := by
  rw [polynomialSymbolicShearDerivation_X_slot, polynomialSymbolicShearSlot_specialization,
    polynomialShearBasis_coordinate_eval]
  apply Finset.sum_congr rfl
  intro a ha
  rw [polynomialShearOrbitParameterCoordinates_eval, polynomialShearRealificationEquiv_repr]
  split_ifs <;> rfl

theorem polynomialShearOrbitSymbolicDerivation_specialization
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t ((symbolicD).val P) =
      (orbitD).val (patchParameterSpecialization t P) := by
  apply polynomialDerivation_intertwine_of_X (patchParameterSpecialization t) (symbolicD).val (orbitD).val
  intro i
  cases i with
  | inl i =>
    rw [polynomialSymbolicShearDerivation_X_parameter, map_zero]
    simp only [patchParameterSpecialization, aeval_X, Sum.elim_inl, MvPolynomial.derivation_C]
  | inr i =>
    rw [patchParameterSpecialization_X_slot]
    exact polynomialShearOrbitSymbolicDerivation_X_slot_specialization w s hw g t i

theorem polynomialShearOrbitSymbolicExp_specialization
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (polynomialShearExp symbolicD P) =
      polynomialShearExp orbitD (patchParameterSpecialization t P) :=
  polynomialShearExp_intertwine (patchParameterSpecialization t) symbolicD orbitD
    (polynomialShearOrbitSymbolicDerivation_specialization w s hw g t) P

end Erdos3

end

section

namespace Erdos3

open MvPolynomial Module VectorPolynomial
open scoped TensorProduct

section Coordinates

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}
variable (s : ℕ) (hw : ∀ i, w i ≤ s) (weight : σ → ℕ)

theorem weightedPolynomialShearReal_adapted_iff_coordinate_support
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)) :
    (polynomialShearFiltration w s hw).realification.Adapted weight p ↔
      ∀ a : PolynomialShearIndex w,
        VectorPolynomial.coordinate
          (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p ∈
          weightedSupportLE weight (polynomialShearDeficit w a) := by
  rw [NilpotentLieFiltration.adapted_iff_coefficients]
  constructor
  · intro hp a α hα
    change α ∈ (VectorPolynomial.coordinate
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p).support at hα
    by_contra hdeg
    have hc := ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
      (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
      (fun j => polynomialShearLayer_span w j) _ _).mp (hp α) a hdeg
    apply (MvPolynomial.mem_support_iff.mp hα)
    rw [VectorPolynomial.coeff_coordinate]
    exact hc
  · intro hp α
    apply ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
      (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
      (fun j => polynomialShearLayer_span w j) _ _).mpr
    intro a ha
    change (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a)
      (VectorPolynomial.coefficients p α) = 0
    have hc : (VectorPolynomial.coordinate
        (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom p).coeff α = 0 := by
      by_contra hne
      exact ha (hp a (MvPolynomial.mem_support_iff.mpr hne))
    exact (VectorPolynomial.coeff_coordinate _ p α).symm.trans hc

noncomputable def weightedPolynomialShearOrbitParameterCoordinates
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit weight)
    (a : PolynomialShearIndex w) : MvPolynomial σ ℝ :=
  VectorPolynomial.coordinate
    (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom g.log

theorem weightedPolynomialShearOrbitParameterCoordinates_degree
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit weight)
    (a : PolynomialShearIndex w) :
    weightedPolynomialShearOrbitParameterCoordinates s hw weight g a ∈
      weightedSupportLE weight (polynomialShearDeficit w a) :=
  (weightedPolynomialShearReal_adapted_iff_coordinate_support s hw weight g.log).mp g.adapted a

theorem weightedPolynomialShearOrbitParameterCoordinates_eval
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit weight)
    (t : σ → ℝ) (a : PolynomialShearIndex w) :
    MvPolynomial.eval t (weightedPolynomialShearOrbitParameterCoordinates s hw weight g a) =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr
        ((polynomialShearFiltration w s hw).realification.polynomialOrbitRealEval
          weight t g).coord a := by
  exact (VectorPolynomial.coordinate_eval₂
    (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a) t g.log).symm

theorem weightedPolynomialShearOrbitParameterCoordinates_reconstruct
    [Fintype (PolynomialShearIndex w)]
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit weight) :
    VectorPolynomial.ofCoordinates ((polynomialShearBasis (R := ℚ) w).baseChange ℝ)
      (weightedPolynomialShearOrbitParameterCoordinates s hw weight g) = g.log :=
  VectorPolynomial.ofCoordinates_coordinate _ _

end Coordinates

variable {σ : Type*} {d : ℕ}

variable (w : Fin d → ℕ) [Fintype (PolynomialShearIndex w)]
variable (s : ℕ) (hw : ∀ i, w i ≤ s) (weight : σ → ℕ)
variable (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit weight)
variable (t : σ → ℝ)

local notation "orbitD" => polynomialShearRealificationEquiv w
  (NilpotentLieBCHGroup.coord
    (NilpotentLieFiltration.polynomialOrbitRealEval
      (NilpotentLieFiltration.realification (polynomialShearFiltration w s hw))
      weight t g))
local notation "symbolicD" => polynomialSymbolicShearDerivation w
  (weightedPolynomialShearOrbitParameterCoordinates s hw weight g)

theorem weightedPolynomialShearOrbitSymbolicDerivation_X_slot_specialization (i : Fin d) :
    patchParameterSpecialization t ((symbolicD).val (X (Sum.inr i))) = (orbitD).val (X i) := by
  rw [polynomialSymbolicShearDerivation_X_slot, polynomialSymbolicShearSlot_specialization,
    polynomialShearBasis_coordinate_eval]
  apply Finset.sum_congr rfl
  intro a ha
  rw [weightedPolynomialShearOrbitParameterCoordinates_eval, polynomialShearRealificationEquiv_repr]
  split_ifs <;> rfl

theorem weightedPolynomialShearOrbitSymbolicDerivation_specialization
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t ((symbolicD).val P) =
      (orbitD).val (patchParameterSpecialization t P) := by
  apply polynomialDerivation_intertwine_of_X (patchParameterSpecialization t) (symbolicD).val (orbitD).val
  intro i
  cases i with
  | inl i =>
    rw [polynomialSymbolicShearDerivation_X_parameter, map_zero]
    simp only [patchParameterSpecialization, aeval_X, Sum.elim_inl, MvPolynomial.derivation_C]
  | inr i =>
    rw [patchParameterSpecialization_X_slot]
    exact weightedPolynomialShearOrbitSymbolicDerivation_X_slot_specialization w s hw weight g t i

theorem weightedPolynomialShearOrbitSymbolicExp_specialization
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (polynomialShearExp symbolicD P) =
      polynomialShearExp orbitD (patchParameterSpecialization t P) :=
  polynomialShearExp_intertwine (patchParameterSpecialization t) symbolicD orbitD
    (weightedPolynomialShearOrbitSymbolicDerivation_specialization w s hw weight g t) P

end Erdos3

end

end OAI
