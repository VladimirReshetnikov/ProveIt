/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.MvPolynomial
import OAI.Compat.TensorProduct
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.UpperLower.Basic
import OAI.Combinatorics.Progressions.Estimates.SquarefreeCoefficients
import OAI.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
import OAI.Combinatorics.Progressions.Polynomial.PolynomialKernelValues

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

@[simp] theorem lie_monomial (α β : σ →₀ ℕ) (a b : L) :
    ⁅monomial (R := R) α a, monomial (R := R) β b⁆ = monomial (R := R) (α + β) ⁅a, b⁆ := by
  simp only [monomial, LieAlgebra.ExtendScalars.bracket_tmul,
    MvPolynomial.monomial_mul_monomial, one_mul]

noncomputable def evalLie (x : σ → R) : VectorPolynomial σ R L →ₗ⁅R⁆ L where
  toLinearMap := eval x
  map_lie' {p q} := by
    change eval x ⁅p, q⁆ = ⁅eval x p, eval x q⁆
    induction p using TensorProduct.inductionOn with
    | tmul a v =>
      induction q using TensorProduct.inductionOn with
      | tmul b w =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, eval_tmul, map_mul,
          smul_lie, lie_smul, smul_smul, mul_comm]
      | add p q hp hq => rw [LieRing.lie_add, map_add, hp, hq, map_add, LieRing.lie_add]
    | add p q hp hq => rw [LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]

@[simp] theorem evalLie_apply (x : σ → R) (p : VectorPolynomial σ R L) :
    evalLie x p = eval x p := rfl

section Rational

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem eval_lieBCH (x : σ → ℚ) (s : ℕ) (p q : VectorPolynomial σ ℚ L) :
    eval x (lieBCH s p q) = lieBCH s (eval x p) (eval x q) :=
  map_lieBCH (evalLie x) s p q

theorem lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) s = ⊥ := by
  have hpoly : LieModule.lowerCentralSeries (MvPolynomial σ ℚ)
      (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) s = ⊥ := by
    rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange, hnil, LieSubmodule.baseChange_bot]
  apply SetLike.coe_injective
  change (LieModule.lowerCentralSeries ℚ (VectorPolynomial σ ℚ L)
    (VectorPolynomial σ ℚ L) s : Set (VectorPolynomial σ ℚ L)) = {0}
  rw [LieModule.coe_lowerCentralSeries_eq_int,
    ← LieModule.coe_lowerCentralSeries_eq_int (MvPolynomial σ ℚ)
      (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) s, hpoly]
  rfl

end Rational
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

noncomputable def outsideDownsetIdeal (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) :
    LieIdeal R (VectorPolynomial σ R L) :=
  { coefficientSupport Jᶜ with
    lie_mem := by
      classical
      intro p q hq
      change ∀ a, a ∉ Jᶜ → coefficients q a = 0 at hq
      have hq' : ∀ a ∈ J, coefficients q a = 0 := by
        simpa only [Set.mem_compl_iff, not_not] using hq
      rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
      simp only [Finsupp.sum]
      rw [sum_lie_sum]
      apply (coefficientSupport Jᶜ).sum_mem
      intro a _
      apply (coefficientSupport Jᶜ).sum_mem
      intro b hb
      rw [lie_monomial]
      apply monomial_mem_coefficientSupport
      intro hab
      have hle : b ≤ a + b := by
        intro i
        simp only [Finsupp.add_apply]
        omega
      exact (Finsupp.mem_support_iff.mp hb) (hq' b (hJ hle hab)) }

@[simp] theorem mem_outsideDownsetIdeal (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J)
    (p : VectorPolynomial σ R L) :
    p ∈ outsideDownsetIdeal (R := R) (L := L) J hJ ↔ ∀ a ∈ J, coefficients p a = 0 := by
  change (∀ a, a ∉ Jᶜ → coefficients p a = 0) ↔ _
  simp only [Set.mem_compl_iff, not_not]

theorem outsideDownsetIdeal_union (J K : Set (σ →₀ ℕ))
    (hJ : IsLowerSet J) (hK : IsLowerSet K) :
    outsideDownsetIdeal (R := R) (L := L) (J ∪ K) (hJ.union hK) =
      outsideDownsetIdeal J hJ ⊓ outsideDownsetIdeal K hK := by
  ext p
  simp only [LieSubmodule.mem_inf, mem_outsideDownsetIdeal, Set.mem_union, or_imp,
    forall_and]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R S L : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [LieRing L] [LieAlgebra R L] [LieAlgebra S L] [IsScalarTower R S L]

noncomputable def eval₂Lie (x : σ → S) : VectorPolynomial σ R L →ₗ⁅R⁆ L where
  toLinearMap := eval₂ x
  map_lie' {p q} := by
    change eval₂ x ⁅p, q⁆ = ⁅eval₂ x p, eval₂ x q⁆
    induction p using TensorProduct.inductionOn with
    | tmul a v =>
      induction q using TensorProduct.inductionOn with
      | tmul b w =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, eval₂_tmul, map_mul,
          smul_lie, lie_smul, smul_smul, mul_comm]
      | add p q hp hq => rw [LieRing.lie_add, map_add, hp, hq, map_add, LieRing.lie_add]
    | add p q hp hq => rw [LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]

@[simp] theorem eval₂Lie_apply (x : σ → S) (p : VectorPolynomial σ R L) :
    eval₂Lie (R := R) (L := L) x p = eval₂ x p := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module

section Values

variable {σ K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

theorem eq_zero_of_eval_zero (p : VectorPolynomial σ K V) (hp : ∀ x : σ → K, eval x p = 0) : p = 0 := by
  let b := Module.Free.chooseBasis K V
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  have hc : coordinate (b.coord i).toAddMonoidHom p = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_zero, ← coordinate_eval₂]
    have he : eval₂ x p = 0 := by
      simpa using (eval₂_algebraMap (S := K) x p).trans (hp x)
    rw [he, map_zero]
  have h := congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff α) hc
  simp only [coeff_coordinate, AddMonoidAlgebra.coeff_zero] at h
  change b.repr (coefficients p α) i = 0 at h
  simpa only [map_zero, Finsupp.zero_apply] using h

theorem eval_mem_iff_coefficients (U : Submodule K V) (p : VectorPolynomial σ K V) :
    (∀ x : σ → K, eval x p ∈ U) ↔ ∀ α, coefficients p α ∈ U := by
  constructor
  · intro hp
    have hz : map U.mkQ p = 0 := by
      apply eq_zero_of_eval_zero
      intro x
      rw [eval_map]
      exact (Submodule.Quotient.mk_eq_zero U).mpr (hp x)
    intro α
    apply (Submodule.Quotient.mk_eq_zero U).mp
    change U.mkQ (coefficients p α) = 0
    have hc := congrArg (fun q : VectorPolynomial σ K (V ⧸ U) => coefficients q α) hz
    simpa only [coefficients_map, map_zero, Finsupp.zero_apply] using hc
  · intro hp x
    classical
    rw [← sum_monomial_coefficients p]
    simp only [Finsupp.sum, map_sum, eval_monomial]
    exact U.sum_mem (fun α _ => U.smul_mem _ (hp α))

end Values

section Lie

variable {σ K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]

noncomputable def coefficientSubmodule (U : Submodule K L) : Submodule K (VectorPolynomial σ K L) where
  carrier := {p | ∀ α, coefficients p α ∈ U}
  zero_mem' := by intro α; simp
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using U.add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using U.smul_mem c (hp α)

theorem monomial_mem_coefficientSubmodule (U : Submodule K L) (α : σ →₀ ℕ) {v : L} (hv : v ∈ U) :
    monomial (R := K) α v ∈ coefficientSubmodule U := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hv
  · simp [h]

noncomputable def coefficientLieSubalgebra (U : LieSubalgebra K L) :
    LieSubalgebra K (VectorPolynomial σ K L) :=
  { coefficientSubmodule U.toSubmodule with
    lie_mem' := by
      intro p q hp hq
      classical
      rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
      simp only [Finsupp.sum]
      rw [sum_lie_sum (coefficients p).support (coefficients q).support
        (fun α => monomial (R := K) α (coefficients p α))
        (fun β => monomial (R := K) β (coefficients q β))]
      apply Submodule.sum_mem
      intro α _
      apply Submodule.sum_mem
      intro β _
      rw [lie_monomial]
      exact monomial_mem_coefficientSubmodule U.toSubmodule _ (U.lie_mem (hp α) (hq β)) }

end Lie

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open VectorPolynomial

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem coefficient_zero_of_squarefreeKernel (p : VectorPolynomial ι ℚ L)
    (hp : p ∈ LinearMap.ker squarefreeCoefficients) (a : ι →₀ ℕ) (ha : SquarefreeExponent a) :
    coefficients p a = 0 :=
  congrFun (LinearMap.mem_ker.mp hp) ⟨a, ha⟩

theorem squarefreeKernel_lie_mem (p q : VectorPolynomial ι ℚ L)
    (hq : q ∈ LinearMap.ker squarefreeCoefficients) :
    ⁅p, q⁆ ∈ LinearMap.ker squarefreeCoefficients := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p).support (coefficients q).support
    (fun a => monomial (R := ℚ) a (coefficients p a))
    (fun b => monomial (R := ℚ) b (coefficients q b))]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  rw [lie_monomial]
  by_cases hb : SquarefreeExponent b
  · rw [coefficient_zero_of_squarefreeKernel q hq b hb, lie_zero]
    simpa only [monomial, TensorProduct.tmul_zero] using
      (LinearMap.ker (squarefreeCoefficients (ι := ι) (L := L))).zero_mem
  · exact monomial_mem_squarefreeKernel (a + b) (not_squarefreeExponent_add_right a b hb) _

noncomputable def squarefreePolynomialIdeal : LieIdeal ℚ (VectorPolynomial ι ℚ L) :=
  { LinearMap.ker squarefreeCoefficients with
    lie_mem := fun {p q} hq => squarefreeKernel_lie_mem p q hq }

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def weightedDilation (w : σ → ℕ) (r : R) :
    VectorPolynomial σ R V →ₗ[R] VectorPolynomial σ R V where
  toFun p := coefficients.symm (Finsupp.onFinset (coefficients p).support
    (fun α => r ^ Finsupp.weight w α • coefficients p α) (by
      intro α hα
      apply Finsupp.mem_support_iff.mpr
      intro hz
      exact hα (by rw [hz, smul_zero])))
  map_add' p q := by
    apply coefficients.injective
    ext α
    simp only [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply,
      map_add, Finsupp.add_apply, smul_add]
  map_smul' c p := by
    apply coefficients.injective
    ext α
    simp only [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply,
      map_smul, Finsupp.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

@[simp] theorem coefficients_weightedDilation (w : σ → ℕ) (r : R)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (weightedDilation w r p) α = r ^ Finsupp.weight w α • coefficients p α := by
  simp only [weightedDilation, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
    Finsupp.onFinset_apply]

theorem weightedDilation_monomial (w : σ → ℕ) (r : R) (α : σ →₀ ℕ) (v : V) :
    weightedDilation w r (monomial α v) = r ^ Finsupp.weight w α • monomial α v := by
  classical
  apply coefficients.injective
  ext β
  by_cases h : α = β <;> simp [h]

@[simp] theorem weightedDilation_one (w : σ → ℕ) (p : VectorPolynomial σ R V) :
    weightedDilation w 1 p = p := by
  apply coefficients.injective
  ext α
  simp

theorem weightedDilation_mul (w : σ → ℕ) (a b : R) (p : VectorPolynomial σ R V) :
    weightedDilation w (a * b) p = weightedDilation w a (weightedDilation w b p) := by
  apply coefficients.injective
  ext α
  simp only [coefficients_weightedDilation, mul_pow, smul_smul]

theorem weighted_monomial_dilation (w : σ → ℕ) (r : R) (x : σ → R) (α : σ →₀ ℕ) :
    α.prod (fun i n => (r ^ w i * x i) ^ n) =
      r ^ Finsupp.weight w α * α.prod (fun i n => x i ^ n) := by
  classical
  simp only [Finsupp.prod, mul_pow, ← pow_mul, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.mul_comm _ _

theorem eval_weightedDilation (w : σ → ℕ) (r : R) (x : σ → R)
    (p : VectorPolynomial σ R V) :
    eval x (weightedDilation w r p) = eval (fun i => r ^ w i * x i) p := by
  classical
  rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, weightedDilation_monomial, map_smul, eval_monomial,
    weighted_monomial_dilation, smul_smul]

theorem eval₂_weightedDilation {S : Type*} [CommRing S] [Algebra R S]
    [Module S V] [IsScalarTower R S V]
    (w : σ → ℕ) (r : R) (x : σ → S) (p : VectorPolynomial σ R V) :
    eval₂ x (weightedDilation w r p) =
      eval₂ (fun i => (algebraMap R S r) ^ w i * x i) p := by
  classical
  rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, weightedDilation_monomial, map_smul, eval₂_monomial]
  apply Finset.sum_congr rfl
  intro α _
  rw [weighted_monomial_dilation, ← map_pow (algebraMap R S) r (Finsupp.weight w α),
    mul_smul, IsScalarTower.algebraMap_smul]

section Lie

variable {L : Type*} [LieRing L] [LieAlgebra R L]

theorem weightedDilation_lie (w : σ → ℕ) (r : R) (p q : VectorPolynomial σ R L) :
    weightedDilation w r ⁅p, q⁆ = ⁅weightedDilation w r p, weightedDilation w r q⁆ := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum, map_sum, sum_lie_sum, weightedDilation_monomial,
    lie_monomial, map_add, pow_add]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [smul_lie (r ^ Finsupp.weight w α) (monomial (R := R) α (coefficients p α))
      (r ^ Finsupp.weight w β • monomial (R := R) β (coefficients q β)),
    lie_smul (r ^ Finsupp.weight w β) (monomial (R := R) α (coefficients p α))
      (monomial (R := R) β (coefficients q β)),
    lie_monomial, smul_smul]

noncomputable def weightedDilationLie (w : σ → ℕ) (r : R) :
    VectorPolynomial σ R L →ₗ⁅R⁆ VectorPolynomial σ R L :=
  { weightedDilation w r with map_lie' := by intro p q; exact weightedDilation_lie w r p q }

end Lie
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

noncomputable def translate (h : σ → R) : VectorPolynomial σ R V →ₗ[R] VectorPolynomial σ R V :=
  (polynomialTranslate h).toLinearMap.rTensor V

@[simp] theorem translate_tmul (h : σ → R) (p : MvPolynomial σ R) (v : V) :
    translate h (p ⊗ₜ[R] v) = polynomialTranslate h p ⊗ₜ[R] v := rfl

theorem coefficients_translate_monomial (h : σ → R) (α β : σ →₀ ℕ) (v : V) :
    coefficients (translate h (monomial α v)) β =
      (polynomialTranslate h (MvPolynomial.monomial α 1)).coeff β • v := by
  rw [monomial, translate_tmul, coefficients_tmul]

theorem coefficients_translate_sub_monomial (h : σ → R) (α β : σ →₀ ℕ) (v : V) :
    coefficients (translate h (monomial α v) - monomial α v) β =
      (polynomialTranslate h (MvPolynomial.monomial α 1) -
        MvPolynomial.monomial α 1).coeff β • v := by
  rw [monomial, translate_tmul, ← TensorProduct.sub_tmul, coefficients_tmul]

theorem eval_translate (h x : σ → R) (p : VectorPolynomial σ R V) :
    eval x (translate h p) = eval (fun i => x i + h i) p := by
  induction p using TensorProduct.inductionOn with
  | tmul q v =>
    simp only [translate_tmul, eval_tmul]
    congr 1
    rw [polynomialTranslate, MvPolynomial.comp_aeval_apply]
    simp
  | add p q hp hq => simp only [map_add, hp, hq]

theorem map_translate (h : σ → R) (f : V →ₗ[R] W) (p : VectorPolynomial σ R V) :
    map f (translate h p) = translate h (map f p) := by
  induction p using TensorProduct.inductionOn with
  | tmul q v => rfl
  | add p q hp hq => simp only [map_add, hp, hq]

theorem coefficients_translate (h : σ → R) (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (translate h p) α = ∑ β ∈ (coefficients p).support,
      (polynomialTranslate h (MvPolynomial.monomial β 1)).coeff α • coefficients p β := by
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply, coefficients_translate_monomial]

theorem coefficients_translate_sub (h : σ → R) (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (translate h p - p) α = ∑ β ∈ (coefficients p).support,
      (polynomialTranslate h (MvPolynomial.monomial β 1) -
        MvPolynomial.monomial β 1).coeff α • coefficients p β := by
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, ← Finset.sum_sub_distrib,
    Finsupp.finsetSum_apply, coefficients_translate_sub_monomial]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped TensorProduct

variable {σ R S V W : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
  [AddCommGroup W] [Module R W] [Module S W] [IsScalarTower R S W]

theorem eval₂_map (f : V →ₗ[S] W) (x : σ → S) (p : VectorPolynomial σ R V) :
    eval₂ x (map (f.restrictScalars R) p) = f (eval₂ x p) := by
  induction p using TensorProduct.inductionOn with
  | tmul q v =>
    change eval₂ x (q ⊗ₜ[R] f v) = f (eval₂ x (q ⊗ₜ[R] v))
    rw [eval₂_tmul, eval₂_tmul, map_smul]
  | add p q hp hq => simp only [map_add, hp, hq]

section Field

variable {K : Type*} [Field K] [Infinite K] [Algebra R K]
  [Module K V] [IsScalarTower R K V]

theorem eq_zero_of_eval₂_zero (p : VectorPolynomial σ R V) (hp : ∀ x : σ → K, eval₂ x p = 0) :
    p = 0 := by
  let b := Module.Free.chooseBasis K V
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  have hc : coordinate (b.coord i).toAddMonoidHom p = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_zero, ← coordinate_eval₂, hp, map_zero]
  have h := congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff α) hc
  simp only [coeff_coordinate, AddMonoidAlgebra.coeff_zero] at h
  change b.repr (coefficients p α) i = 0 at h
  simpa only [map_zero, Finsupp.zero_apply] using h

theorem eval₂_mem_iff_coefficients (U : Submodule K V) (p : VectorPolynomial σ R V) :
    (∀ x : σ → K, eval₂ x p ∈ U) ↔ ∀ α, coefficients p α ∈ U := by
  constructor
  · intro hp
    have hz : map (U.mkQ.restrictScalars R) p = 0 := by
      apply eq_zero_of_eval₂_zero (K := K)
      intro x
      rw [eval₂_map]
      exact (Submodule.Quotient.mk_eq_zero U).mpr (hp x)
    intro α
    apply (Submodule.Quotient.mk_eq_zero U).mp
    change U.mkQ (coefficients p α) = 0
    have hc := congrArg (fun q : VectorPolynomial σ R (V ⧸ U) => coefficients q α) hz
    simpa only [coefficients_map, LinearMap.restrictScalars_apply, map_zero, Finsupp.zero_apply] using hc
  · intro hp x
    classical
    rw [← sum_monomial_coefficients p]
    simp only [Finsupp.sum, map_sum, eval₂_monomial]
    exact U.sum_mem (fun α _ => U.smul_mem _ (hp α))

end Field

end Erdos3.VectorPolynomial

end

end OAI
