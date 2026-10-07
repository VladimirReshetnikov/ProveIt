/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.Algebra.MvPolynomial.Monad
import OAI.Combinatorics.Progressions.Estimates.LinearCoefficientMap
import OAI.Combinatorics.Progressions.Estimates.ScalarExtensionSubstitution
import OAI.Combinatorics.Progressions.Geometry.WeightedSubstitutionSupport
import OAI.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
import OAI.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues

namespace OAI


namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

noncomputable def parameterLinearCoordinate {I K : Type*} [Fintype K] (j : I) :
    MvPolynomial (K × I) (MvPolynomial K ℝ) := ∑ k, C (X k) * X (k, j)

noncomputable def parameterPolynomialPullback {I K : Type*} [Fintype K] :
    MvPolynomial I ℝ →ₐ[ℝ] MvPolynomial (K × I) (MvPolynomial K ℝ) :=
  aeval parameterLinearCoordinate

theorem parameterPolynomialPullback_degree {I K : Type*} [Fintype K]
    (P : MvPolynomial I ℝ) {d : ℕ} (hP : P.totalDegree ≤ d) :
    (parameterPolynomialPullback (K := K) P).totalDegree ≤ d := by
  have hc (j : I) : (parameterLinearCoordinate (K := K) j).totalDegree ≤ 1 := by
    apply totalDegree_finsetSum_le
    intro k _
    exact (totalDegree_mul _ _).trans (by simp)
  simpa only [parameterPolynomialPullback, Nat.mul_one] using
    aeval_polynomial_totalDegree_le P parameterLinearCoordinate hP hc

theorem parameterPolynomialPullback_eval {I K : Type*} [Fintype K]
    (P : MvPolynomial I ℝ) (v : K → I → ℝ) :
    eval (fun z => C (v z.1 z.2)) (parameterPolynomialPullback P) =
      aeval (fun j => rowPolynomial (fun k => v k j)) P := by
  let E : MvPolynomial (K × I) (MvPolynomial K ℝ) →ₐ[ℝ] MvPolynomial K ℝ :=
    (aeval (fun z : K × I => C (v z.1 z.2))).restrictScalars ℝ
  have he : E.comp parameterPolynomialPullback =
      aeval (fun j => rowPolynomial (fun k => v k j)) := by
    apply algHom_ext
    intro j
    simp [E, parameterPolynomialPullback, parameterLinearCoordinate, rowPolynomial, mul_comm]
  exact AlgHom.congr_fun he P

end Erdos3


namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ τ υ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

noncomputable def substitute (f : σ → MvPolynomial τ R) :
    VectorPolynomial σ R V →ₗ[R] VectorPolynomial τ R V :=
  (MvPolynomial.aeval (R := R) f).toLinearMap.rTensor V

@[simp] theorem substitute_tmul (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) (v : V) :
    substitute f (p ⊗ₜ[R] v) = MvPolynomial.aeval (R := R) f p ⊗ₜ[R] v := rfl

theorem coefficients_substitute_monomial (f : σ → MvPolynomial τ R)
    (α : σ →₀ ℕ) (β : τ →₀ ℕ) (v : V) :
    coefficients (substitute f (monomial α v)) β =
      (MvPolynomial.aeval (R := R) f (MvPolynomial.monomial α 1)).coeff β • v := by
  rw [monomial, substitute_tmul, coefficients_tmul]

theorem coefficients_substitute (f : σ → MvPolynomial τ R) (p : VectorPolynomial σ R V)
    (α : τ →₀ ℕ) :
    coefficients (substitute f p) α = ∑ β ∈ (coefficients p).support,
      (MvPolynomial.aeval (R := R) f (MvPolynomial.monomial β 1)).coeff α • coefficients p β := by
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply, coefficients_substitute_monomial]

theorem eval_substitute (f : σ → MvPolynomial τ R) (x : τ → R) (p : VectorPolynomial σ R V) :
    eval x (substitute f p) = eval (fun i => MvPolynomial.aeval (R := R) x (f i)) p := by
  induction p using TensorProduct.inductionOn with
  | tmul q v =>
    simp only [substitute_tmul, eval_tmul]
    rw [MvPolynomial.comp_aeval_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem map_substitute (f : σ → MvPolynomial τ R) (g : V →ₗ[R] W)
    (p : VectorPolynomial σ R V) :
    map g (substitute f p) = substitute f (map g p) := by
  induction p using TensorProduct.inductionOn with
  | tmul q v => rfl
  | add p q hp hq => simp only [map_add, hp, hq]

theorem substitute_comp (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R)
    (p : VectorPolynomial σ R V) :
    substitute g (substitute f p) = substitute (fun i => MvPolynomial.aeval (R := R) g (f i)) p := by
  induction p using TensorProduct.inductionOn with
  | tmul q v =>
    simp only [substitute_tmul]
    rw [MvPolynomial.comp_aeval_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem substitute_X (p : VectorPolynomial σ R V) :
    substitute (fun i => MvPolynomial.X i) p = p := by
  induction p using TensorProduct.inductionOn with
  | tmul q v => simp only [substitute_tmul, MvPolynomial.aeval_X_left_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

noncomputable def substituteLie {L : Type*} [LieRing L] [LieAlgebra R L]
    (f : σ → MvPolynomial τ R) :
    VectorPolynomial σ R L →ₗ⁅R⁆ VectorPolynomial τ R L where
  toLinearMap := substitute f
  map_lie' {p q} := by
    change substitute f ⁅p, q⁆ = ⁅substitute f p, substitute f q⁆
    induction p using TensorProduct.inductionOn with
    | tmul a v =>
      induction q using TensorProduct.inductionOn with
      | tmul b w => simp only [LieAlgebra.ExtendScalars.bracket_tmul, substitute_tmul, map_mul]
      | add p q hp hq => rw [LieRing.lie_add, map_add, hp, hq, map_add, LieRing.lie_add]
    | add p q hp hq => rw [LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]

end Erdos3.VectorPolynomial


namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct Classical

noncomputable def coefficientModePolynomial {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W) :
    MvPolynomial (K × I) ℝ :=
  ∑ d ∈ (coefficients p).support,
    mapPolynomialCoefficients ((TensorProduct.curry L).flip (coefficients p d))
      (parameterPolynomialPullback (MvPolynomial.monomial d 1))

theorem coefficientModePolynomial_eval {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    (v : K → I → ℝ) :
    MvPolynomial.eval (fun z => v z.1 z.2) (coefficientModePolynomial L p) =
      L (substitute (fun j => rowPolynomial (fun k => v k j)) p) := by
  unfold coefficientModePolynomial
  rw [map_sum]
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, monomial, substitute_tmul,
    mapPolynomialCoefficients_eval, MvPolynomial.algebraMap_eq, parameterPolynomialPullback_eval]
  rfl

theorem coefficientModePolynomial_degree {I K W : Type*} [Fintype K]
    [AddCommGroup W] [Module ℝ W]
    (L : VectorPolynomial K ℝ W →ₗ[ℝ] ℝ) (p : VectorPolynomial I ℝ W)
    {h : ℕ} (hp : Homogeneous h p) :
    (coefficientModePolynomial L p).totalDegree ≤ h := by
  unfold coefficientModePolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  apply (mapPolynomialCoefficients_degree _ _).trans
  apply parameterPolynomialPullback_degree
  have hsum : d.sum (fun _ n => n) = h := by
    simpa only [Finsupp.degree_eq_weight_one, Finsupp.weight_apply, Pi.one_def,
      smul_eq_mul, mul_one] using homogeneous_support_degree hp hd
  exact (MvPolynomial.totalDegree_monomial_le d 1).trans_eq hsum

end Erdos3.VectorPolynomial


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

def Adapted (w : σ → ℕ) (p : VectorPolynomial σ ℚ L) : Prop :=
  ∀ i, DegreeLE w i (VectorPolynomial.map (F.layer (i + 1)).mkQ p)

theorem adapted_iff_coefficients (w : σ → ℕ) (p : VectorPolynomial σ ℚ L) :
    F.Adapted w p ↔ ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α) := by
  constructor
  · intro hp α
    generalize hd : Finsupp.weight w α = d
    cases d with
    | zero =>
      apply F.antitone (Nat.zero_le 1)
      simp [F.one_eq_top]
    | succ d =>
      have h := hp d α (by rw [hd]; exact Nat.lt_succ_self d)
      rw [coefficients_map] at h
      exact (Submodule.Quotient.mk_eq_zero _).mp h
  · intro hp i α hα
    rw [coefficients_map]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (F.antitone hα (hp α))

noncomputable def adaptedSubmodule (w : σ → ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α)}
  zero_mem' := by intro α; simp
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (F.layer _).add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer _).smul_mem c (hp α)

theorem mem_adaptedSubmodule (w : σ → ℕ) (p : VectorPolynomial σ ℚ L) :
    p ∈ F.adaptedSubmodule w ↔ F.Adapted w p := (F.adapted_iff_coefficients w p).symm

theorem monomial_mem_adaptedSubmodule (w : σ → ℕ) (α : σ →₀ ℕ) {a : L}
    (ha : a ∈ F.layer (Finsupp.weight w α)) :
    monomial (R := ℚ) α a ∈ F.adaptedSubmodule w := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa using ha
  · simp [h]

theorem lie_mem_adaptedSubmodule (w : σ → ℕ) {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.adaptedSubmodule w) (hq : q ∈ F.adaptedSubmodule w) :
    ⁅p, q⁆ ∈ F.adaptedSubmodule w := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p).support (coefficients q).support
    (fun α => monomial (R := ℚ) α (coefficients p α))
    (fun β => monomial (R := ℚ) β (coefficients q β))]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.sum_mem
  intro β _
  rw [lie_monomial]
  apply F.monomial_mem_adaptedSubmodule
  rw [map_add]
  exact F.lie_mem (hp α) (hq β)

noncomputable def adaptedLieSubalgebra (w : σ → ℕ) : LieSubalgebra ℚ (VectorPolynomial σ ℚ L) :=
  { F.adaptedSubmodule w with lie_mem' := F.lie_mem_adaptedSubmodule w }

theorem adapted_bch (w : σ → ℕ) {p q : VectorPolynomial σ ℚ L}
    (hp : F.Adapted w p) (hq : F.Adapted w q) : F.Adapted w (lieBCH s p q) := by
  apply (F.mem_adaptedSubmodule w _).mp
  exact lieBCH_mem (F.adaptedLieSubalgebra w) s
    ((F.mem_adaptedSubmodule w _).mpr hp) ((F.mem_adaptedSubmodule w _).mpr hq)

theorem adapted_neg (w : σ → ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : F.Adapted w p) : F.Adapted w (-p) := by
  exact (F.mem_adaptedSubmodule w _).mp
    ((F.adaptedSubmodule w).neg_mem ((F.mem_adaptedSubmodule w _).mpr hp))

theorem adapted_degreeLE (w : σ → ℕ) {p : VectorPolynomial σ ℚ L}
    (hp : F.Adapted w p) : DegreeLE w s p := by
  intro α hα
  have h := F.antitone hα ((F.adapted_iff_coefficients w p).mp hp α)
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem adapted_map (H : NilpotentLieFiltration M t) (f : L →ₗ[ℚ] M)
    (hf : ∀ i, ∀ a ∈ F.layer i, f a ∈ H.layer i)
    (w : σ → ℕ) {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) :
    H.Adapted w (VectorPolynomial.map f p) := by
  apply (H.adapted_iff_coefficients w _).mpr
  intro α
  rw [coefficients_map]
  exact hf _ _ ((F.adapted_iff_coefficients w p).mp hp α)

theorem exists_adapted_lift (H : NilpotentLieFiltration M t)
    (π : L →ₗ[ℚ] M) (j : M →ₗ[ℚ] L) (hj : Function.RightInverse j π)
    (hlayer : ∀ i, ∀ b ∈ H.layer i, j b ∈ F.layer i)
    (w : σ → ℕ) (p : VectorPolynomial σ ℚ M) (hp : H.Adapted w p) :
    ∃ q : VectorPolynomial σ ℚ L, F.Adapted w q ∧ VectorPolynomial.map π q = p := by
  refine ⟨VectorPolynomial.map j p, H.adapted_map F j hlayer w hp, ?_⟩
  apply coefficients.injective
  ext α
  simp only [coefficients_map]
  exact hj _

end Erdos3.NilpotentLieFiltration


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def polynomialSubgroup (w : σ → ℕ) :
    Subgroup (NilpotentLieBCHGroup (VectorPolynomial σ ℚ L) s
      (VectorPolynomial.lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot)) :=
  NilpotentLieBCHGroup.subgroup (F.adaptedLieSubalgebra w)

abbrev PolynomialOrbit (w : σ → ℕ) : Type _ := ↥(F.polynomialSubgroup w)

variable {F}

def PolynomialOrbit.log {w : σ → ℕ} (p : F.PolynomialOrbit w) : VectorPolynomial σ ℚ L :=
  p.val.coord

theorem PolynomialOrbit.adapted {w : σ → ℕ} (p : F.PolynomialOrbit w) : F.Adapted w p.log :=
  (F.mem_adaptedSubmodule w p.log).mp p.property

theorem PolynomialOrbit.degreeLE {w : σ → ℕ} (p : F.PolynomialOrbit w) :
    DegreeLE w s p.log := F.adapted_degreeLE w p.adapted

def polynomialOrbitOfLog {w : σ → ℕ} (p : VectorPolynomial σ ℚ L) (hp : F.Adapted w p) :
    F.PolynomialOrbit w := ⟨⟨p⟩, (F.mem_adaptedSubmodule w p).mpr hp⟩

@[simp] theorem polynomialOrbitOfLog_log {w : σ → ℕ}
    (p : VectorPolynomial σ ℚ L) (hp : F.Adapted w p) :
    (polynomialOrbitOfLog p hp).log = p := rfl

variable (F)

noncomputable def polynomialOrbitEval (w : σ → ℕ) (x : σ → ℤ) :
    F.PolynomialOrbit w →* F.Group :=
  (NilpotentLieBCHGroup.map (evalLie (fun i => (x i : ℚ)))).comp
    (F.polynomialSubgroup w).subtype

@[simp] theorem polynomialOrbitEval_coord (w : σ → ℕ)
    (p : F.PolynomialOrbit w) (x : σ → ℤ) :
    (F.polynomialOrbitEval w x p).coord = eval (fun i => (x i : ℚ)) p.log := rfl

theorem polynomialOrbitEval_mul (w : σ → ℕ)
    (p q : F.PolynomialOrbit w) (x : σ → ℤ) :
    F.polynomialOrbitEval w x (p * q) = F.polynomialOrbitEval w x p * F.polynomialOrbitEval w x q :=
  map_mul (F.polynomialOrbitEval w x) p q

theorem polynomialOrbitEval_inv (w : σ → ℕ) (p : F.PolynomialOrbit w) (x : σ → ℤ) :
    F.polynomialOrbitEval w x p⁻¹ = (F.polynomialOrbitEval w x p)⁻¹ :=
  map_inv (F.polynomialOrbitEval w x) p

theorem exists_polynomialOrbit_lift (H : NilpotentLieFiltration M t)
    (π : L →ₗ[ℚ] M) (j : M →ₗ[ℚ] L) (hj : Function.RightInverse j π)
    (hlayer : ∀ i, ∀ b ∈ H.layer i, j b ∈ F.layer i)
    (w : σ → ℕ) (p : H.PolynomialOrbit w) :
    ∃ q : F.PolynomialOrbit w,
      ∀ x : σ → ℤ, π (F.polynomialOrbitEval w x q).coord = (H.polynomialOrbitEval w x p).coord := by
  refine ⟨polynomialOrbitOfLog (VectorPolynomial.map j p.log)
    (H.adapted_map F j hlayer w p.adapted), ?_⟩
  intro x
  simp only [polynomialOrbitEval_coord, polynomialOrbitOfLog_log, eval_map]
  exact hj _

theorem polynomialOrbitEval_step_zero (F : NilpotentLieFiltration L 0)
    (w : σ → ℕ) (p : F.PolynomialOrbit w) (x : σ → ℤ) :
    F.polynomialOrbitEval w x p = 1 := by
  apply NilpotentLieBCHGroup.ext
  change (F.polynomialOrbitEval w x p).coord = 0
  have h : (F.polynomialOrbitEval w x p).coord ∈ F.layer 1 := by simp [F.one_eq_top]
  simpa only [F.terminal, Submodule.mem_bot] using h

end Erdos3.NilpotentLieFiltration


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def restrictLieSubalgebra (K : LieSubalgebra ℚ L) : NilpotentLieFiltration K s where
  layer i := (F.layer i).comap K.incl.toLinearMap
  antitone := fun _ _ hij _ hx => F.antitone hij hx
  one_eq_top := by simp only [F.one_eq_top, Submodule.comap_top]
  lie_mem := fun ha hb => F.lie_mem ha hb
  terminal := by
    ext a
    change (a : L) ∈ F.layer (s + 1) ↔ a = 0
    rw [F.terminal, Submodule.mem_bot]
    constructor
    · intro h
      exact Subtype.val_injective h
    · intro h
      rw [h]
      rfl

noncomputable def polynomialLayer (i : ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈ F.layer i}
  zero_mem' := by intro α; simp
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (F.layer i).add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer i).smul_mem c (hp α)

theorem monomial_mem_polynomialLayer (i : ℕ) (α : σ →₀ ℕ) {a : L} (ha : a ∈ F.layer i) :
    monomial (R := ℚ) α a ∈ F.polynomialLayer i := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa using ha
  · simp [h]

theorem lie_mem_polynomialLayer {i j : ℕ} {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.polynomialLayer i) (hq : q ∈ F.polynomialLayer j) :
    ⁅p, q⁆ ∈ F.polynomialLayer (i + j) := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p).support (coefficients q).support
    (fun α => monomial (R := ℚ) α (coefficients p α))
    (fun β => monomial (R := ℚ) β (coefficients q β))]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.sum_mem
  intro β _
  rw [lie_monomial]
  exact F.monomial_mem_polynomialLayer _ _ (F.lie_mem (hp α) (hq β))

noncomputable def polynomialFiltration : NilpotentLieFiltration (VectorPolynomial σ ℚ L) s where
  layer := F.polynomialLayer
  antitone := fun _ _ hij _ hp α => F.antitone hij (hp α)
  one_eq_top := by
    apply top_unique
    intro p _ α
    simp [F.one_eq_top]
  lie_mem := F.lie_mem_polynomialLayer
  terminal := by
    apply bot_unique
    intro p hp
    change p = 0
    apply coefficients.injective
    ext α
    have h := hp α
    simpa only [F.terminal, Submodule.mem_bot, map_zero, Finsupp.zero_apply] using h

noncomputable def adaptedPolynomialFiltration (w : σ → ℕ) :
    NilpotentLieFiltration (F.adaptedLieSubalgebra w) s :=
  F.polynomialFiltration.restrictLieSubalgebra (F.adaptedLieSubalgebra w)

end Erdos3.NilpotentLieFiltration


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adapted_substitute (w : σ → ℕ) (v : τ → ℕ) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) :
    F.Adapted v (VectorPolynomial.substitute f p) := by
  apply (F.adapted_iff_coefficients v _).mpr
  intro α
  rw [coefficients_substitute]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (MvPolynomial.aeval (R := ℚ) f (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ ((F.adapted_iff_coefficients w p).mp hp β)
    exact aeval_monomial_weightedSupport f w v hf β (MvPolynomial.mem_support_iff.mpr hc)

noncomputable def polynomialOrbitSubstitute {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) :
    F.PolynomialOrbit w →* F.PolynomialOrbit v where
  toFun p := polynomialOrbitOfLog (VectorPolynomial.substitute f p.log)
    (F.adapted_substitute w v f hf p.adapted)
  map_one' := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact map_zero (VectorPolynomial.substitute f)
  map_mul' p q := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact map_lieBCH (VectorPolynomial.substituteLie f) s p.log q.log

@[simp] theorem polynomialOrbitSubstitute_log {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    (p : F.PolynomialOrbit w) :
    (F.polynomialOrbitSubstitute f hf p).log = VectorPolynomial.substitute f p.log := rfl

theorem polynomialOrbitSubstitute_eval {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    (p : F.PolynomialOrbit w) (x : τ → ℤ) (y : σ → ℤ)
    (hxy : ∀ i, MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (f i) = (y i : ℚ)) :
    F.polynomialOrbitEval v x (F.polynomialOrbitSubstitute f hf p) = F.polynomialOrbitEval w y p := by
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun j => (x j : ℚ)) (VectorPolynomial.substitute f p.log) = _
  rw [VectorPolynomial.eval_substitute]
  simp only [hxy]
  rfl

end Erdos3.NilpotentLieFiltration

end OAI
