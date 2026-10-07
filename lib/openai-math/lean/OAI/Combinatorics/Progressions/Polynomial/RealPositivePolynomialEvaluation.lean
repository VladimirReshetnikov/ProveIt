/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import Mathlib.LinearAlgebra.Dimension.Constructions
import OAI.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation
import OAI.Combinatorics.Progressions.Nilpotent.VectorPolynomialSupportBracket
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDownsetQuotients
import OAI.Combinatorics.Progressions.Polynomial.RealGradedSymbolPolynomial

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialAlgebra : LieSubalgebra ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | F.Adapted p ∧ coefficients p 0 = 0}
  zero_mem' := by constructor <;> simp [Adapted]
  add_mem' hp hq := ⟨F.adaptedSubmodule.add_mem hp.1 hq.1, by simp [hp.2, hq.2]⟩
  smul_mem' c p hp := ⟨F.adaptedSubmodule.smul_mem c hp.1, by simp [hp.2]⟩
  lie_mem' hp hq := by
    refine ⟨F.lie_mem_adaptedSubmodule hp.1 hq.1, ?_⟩
    rw [← eval_zero_eq_coefficient]
    change evalLie (fun _ : σ => (0 : ℚ)) ⁅_, _⁆ = 0
    rw [LieHom.map_lie]
    simp only [evalLie_apply, eval_zero_eq_coefficient, hp.2, zero_lie]

@[simp] theorem mem_positivePolynomialAlgebra (p : VectorPolynomial σ ℚ L) :
    p ∈ F.positivePolynomialAlgebra ↔ F.Adapted p ∧ coefficients p 0 = 0 := Iff.rfl

theorem positivePolynomial_coefficient_mem (p : F.positivePolynomialAlgebra) (a : σ →₀ ℕ) :
    coefficients p.val a ∈ F.layer (fun i => a i) := p.property.1 a

@[simp] theorem positivePolynomial_constant (p : F.positivePolynomialAlgebra) :
    coefficients p.val 0 = 0 := p.property.2

theorem positivePolynomial_support (p : F.positivePolynomialAlgebra) :
    p.val ∈ coefficientSupport {a : σ →₀ ℕ | a ≠ 0 ∧ (fun i => a i) ≤ bound} := by
  intro a ha
  by_cases hz : a = 0
  · subst a
    exact p.property.2
  · have hb : ¬(fun i => a i) ≤ bound := fun hb => ha ⟨hz, hb⟩
    simpa only [F.terminal _ hb, Submodule.mem_bot] using p.property.1 a

noncomputable def positivePolynomialEvaluation : F.positivePolynomialAlgebra →ₗ⁅ℚ⁆ L :=
  (evalLie (fun _ : σ => (1 : ℚ))).comp F.positivePolynomialAlgebra.incl

theorem positivePolynomialEvaluation_apply (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialEvaluation p = eval (fun _ : σ => (1 : ℚ)) p.val := rfl

theorem positivePolynomial_lowerCentralSeries_eq_bot :
    LieModule.lowerCentralSeries ℚ F.positivePolynomialAlgebra F.positivePolynomialAlgebra s = ⊥ :=
  lie_subalgebra_lowerCentralSeries_eq_bot
    (VectorPolynomial.lowerCentralSeries_eq_bot F.ordinary.lowerCentralSeries_eq_bot)
    F.positivePolynomialAlgebra

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialComponent (a : σ →₀ ℕ) :
    F.positivePolynomialAlgebra →ₗ[ℚ] F.positivePolynomialAlgebra where
  toFun p := ⟨monomial a (coefficients p.val a),
    F.monomial_mem_adaptedSubmodule a (p.property.1 a), by
      classical
      by_cases ha : a = 0
      · subst a
        simp only [coefficients_monomial, Finsupp.single_eq_same, F.positivePolynomial_constant]
      · simp [ha]⟩
  map_add' p q := by
    apply Subtype.ext
    change monomial a (coefficients (p.val + q.val) a) =
      monomial a (coefficients p.val a) + monomial a (coefficients q.val a)
    simp [monomial, TensorProduct.tmul_add]
  map_smul' c p := by
    apply Subtype.ext
    change monomial a (coefficients (c • p.val) a) = c • monomial a (coefficients p.val a)
    simp [monomial]

theorem positivePolynomialComponent_coe (a : σ →₀ ℕ) (p : F.positivePolynomialAlgebra) :
    (F.positivePolynomialComponent a p).val = monomial a (coefficients p.val a) := rfl

theorem sum_positivePolynomialComponent (p : F.positivePolynomialAlgebra) :
    ∑ a ∈ (coefficients p.val).support, F.positivePolynomialComponent a p = p := by
  classical
  apply Subtype.ext
  change F.positivePolynomialAlgebra.incl
    (∑ a ∈ (coefficients p.val).support, F.positivePolynomialComponent a p) = p.val
  rw [map_sum]
  exact sum_monomial_coefficients p.val

theorem positivePolynomialComponent_support (a : σ →₀ ℕ) (p : F.positivePolynomialAlgebra) :
    (F.positivePolynomialComponent a p).val ∈ coefficientSupport ({a} : Set (σ →₀ ℕ)) :=
  monomial_mem_coefficientSupport (Set.mem_singleton a) _

theorem positivePolynomialEvaluation_component (a : σ →₀ ℕ) (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialEvaluation (F.positivePolynomialComponent a p) = coefficients p.val a := by
  change eval (fun _ : σ => (1 : ℚ)) (monomial a (coefficients p.val a)) = _
  simp [eval_monomial, Finsupp.prod]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialDegreeLayer (n : ℕ) :
    Submodule ℚ F.positivePolynomialAlgebra :=
  (coefficientSupport {a : σ →₀ ℕ | n ≤ ∑ i, a i}).comap
    F.positivePolynomialAlgebra.incl.toLinearMap

theorem positivePolynomialDegreeLayer_antitone : Antitone F.positivePolynomialDegreeLayer := by
  intro n m hnm p hp a ha
  exact hp a (fun hm => ha (hnm.trans hm))

theorem positivePolynomialDegreeLayer_one : F.positivePolynomialDegreeLayer 1 = ⊤ := by
  classical
  apply top_unique
  intro p _ a ha
  change ¬1 ≤ ∑ i, a i at ha
  have hs : (∑ i, a i) = 0 := by omega
  have hz : a = 0 := by
    ext i
    have hi : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    simpa only [hs, Nat.le_zero_eq, Finsupp.zero_apply] using hi
  subst a
  exact p.property.2

theorem positivePolynomialDegreeLayer_lie {n m : ℕ} {p q : F.positivePolynomialAlgebra}
    (hp : p ∈ F.positivePolynomialDegreeLayer n) (hq : q ∈ F.positivePolynomialDegreeLayer m) :
    ⁅p, q⁆ ∈ F.positivePolynomialDegreeLayer (n + m) := by
  change ⁅p.val, q.val⁆ ∈ coefficientSupport _
  apply coefficientSupport_lie (S := {a : σ →₀ ℕ | n ≤ ∑ i, a i})
    (T := {a : σ →₀ ℕ | m ≤ ∑ i, a i}) _ hp hq
  intro a ha b hb
  change n + m ≤ ∑ i, (a + b) i
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib] using add_le_add ha hb

theorem positivePolynomialDegreeLayer_terminal :
    F.positivePolynomialDegreeLayer ((∑ i, bound i) + 1) = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply Subtype.ext
  apply coefficients.injective
  ext a
  change coefficients p.val a = 0
  by_cases ha : (fun i => a i) ≤ bound
  · apply hp a
    have hsum : (∑ i, a i) ≤ ∑ i, bound i := Finset.sum_le_sum (fun i _ => ha i)
    change ¬(∑ i, bound i) + 1 ≤ ∑ i, a i
    omega
  · simpa only [F.terminal _ ha, Submodule.mem_bot] using p.property.1 a

noncomputable def positivePolynomialDegreeFiltration :
    NilpotentLieFiltration F.positivePolynomialAlgebra (∑ i, bound i) where
  layer := F.positivePolynomialDegreeLayer
  antitone := F.positivePolynomialDegreeLayer_antitone
  one_eq_top := F.positivePolynomialDegreeLayer_one
  lie_mem := F.positivePolynomialDegreeLayer_lie
  terminal := F.positivePolynomialDegreeLayer_terminal

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open Module VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ}

abbrev BoxedDegreeIndex (bound : σ → ℕ) := ∀ i, Fin (bound i + 1)

noncomputable def boxedDegreeMonomial (a : BoxedDegreeIndex bound) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (a i).val)

@[simp] theorem boxedDegreeMonomial_apply (a : BoxedDegreeIndex bound) (i : σ) :
    boxedDegreeMonomial a i = (a i).val := by
  classical
  exact congrFun (Finsupp.equivFunOnFinite.apply_symm_apply (fun i => (a i).val)) i

variable (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialCoordinates :
    F.positivePolynomialAlgebra →ₗ[ℚ] (BoxedDegreeIndex bound → L) where
  toFun p a := coefficients p.val (boxedDegreeMonomial a)
  map_add' p q := by ext a; simp
  map_smul' c p := by ext a; simp

theorem positivePolynomialCoordinates_injective : Function.Injective F.positivePolynomialCoordinates := by
  classical
  intro p q hpq
  apply Subtype.ext
  apply coefficients.injective
  ext a
  by_cases ha : (fun i => a i) ≤ bound
  · let b : BoxedDegreeIndex bound := fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩
    have hb : boxedDegreeMonomial b = a := by ext i; simp [b]
    have h := congrFun hpq b
    change coefficients p.val (boxedDegreeMonomial b) = coefficients q.val (boxedDegreeMonomial b) at h
    simpa only [hb] using h
  · have hp : coefficients p.val a = 0 := by
      simpa only [F.terminal _ ha, Submodule.mem_bot] using p.property.1 a
    have hq : coefficients q.val a = 0 := by
      simpa only [F.terminal _ ha, Submodule.mem_bot] using q.property.1 a
    rw [hp, hq]

instance positivePolynomialFiniteDimensional [FiniteDimensional ℚ L] :
    FiniteDimensional ℚ F.positivePolynomialAlgebra :=
  FiniteDimensional.of_injective F.positivePolynomialCoordinates F.positivePolynomialCoordinates_injective

theorem positivePolynomial_finrank_le [FiniteDimensional ℚ L] :
    finrank ℚ F.positivePolynomialAlgebra ≤ (∏ i, (bound i + 1)) * finrank ℚ L := by
  classical
  calc
    _ ≤ finrank ℚ (BoxedDegreeIndex bound → L) :=
      LinearMap.finrank_le_finrank_of_injective F.positivePolynomialCoordinates_injective
    _ = ∑ _ : BoxedDegreeIndex bound, finrank ℚ L := Module.finrank_pi_fintype ℚ
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_pi, Fintype.card_fin, Nat.cast_id]

theorem positivePolynomial_finrank_le_total [FiniteDimensional ℚ L] :
    finrank ℚ F.positivePolynomialAlgebra ≤ 2 ^ (∑ i, bound i) * finrank ℚ L := by
  classical
  have h : (∏ i, (bound i + 1)) ≤ 2 ^ (∑ i, bound i) := by
    calc
      _ ≤ ∏ i, 2 ^ bound i := Finset.prod_le_prod (fun i _ => Nat.succ_le_of_lt (Nat.lt_two_pow_self))
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum]
  exact F.positivePolynomial_finrank_le.trans (Nat.mul_le_mul_right _ h)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realPositivePolynomialMap :
    (ℝ ⊗[ℚ] F.positivePolynomialAlgebra) →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  VectorPolynomial.realificationLieEquiv.toLieHom.comp
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) F.positivePolynomialAlgebra.incl)

theorem realPositivePolynomialMap_coefficient_tmul
    (r : ℝ) (p : F.positivePolynomialAlgebra) (a : σ →₀ ℕ) :
    coefficients (F.realPositivePolynomialMap (r ⊗ₜ[ℚ] p)) a = r ⊗ₜ[ℚ] coefficients p.val a := by
  change coefficients (VectorPolynomial.realificationLieEquiv (r ⊗ₜ[ℚ] p.val)) a = _
  exact coefficients_realificationLieEquiv_tmul r p.val a

theorem realPositivePolynomialMap_adapted (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    F.realification.Adapted (F.realPositivePolynomialMap x) := by
  intro a
  induction x using TensorProduct.inductionOn with
  | tmul r p =>
    rw [F.realPositivePolynomialMap_coefficient_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem r (p.property.1 a)
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply]
    exact Submodule.add_mem _ hx hy

theorem realPositivePolynomialMap_constant (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    coefficients (F.realPositivePolynomialMap x) 0 = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul r p =>
    rw [F.realPositivePolynomialMap_coefficient_tmul, p.property.2, TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_zero]

noncomputable def realPositivePolynomialTensor :
    (ℝ ⊗[ℚ] F.positivePolynomialAlgebra) →ₗ⁅ℚ⁆ F.realification.positivePolynomialAlgebra where
  toLinearMap := F.realPositivePolynomialMap.toLinearMap.codRestrict
    F.realification.positivePolynomialAlgebra.toSubmodule
    (fun x => ⟨F.realPositivePolynomialMap_adapted x, F.realPositivePolynomialMap_constant x⟩)
  map_lie' {x y} := by
    apply Subtype.ext
    exact F.realPositivePolynomialMap.map_lie x y

theorem realPositivePolynomialTensor_coe (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    (F.realPositivePolynomialTensor x).val = F.realPositivePolynomialMap x := rfl

theorem realPositivePolynomialTensor_injective : Function.Injective F.realPositivePolynomialTensor := by
  intro x y h
  apply realification_subtype_injective F.positivePolynomialAlgebra.toSubmodule
  apply VectorPolynomial.realificationLieEquiv.injective
  exact congrArg Subtype.val h

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def positivePolynomialMultidegreeLayer (a : σ → ℕ) :
    Submodule ℚ F.positivePolynomialAlgebra :=
  (coefficientSupport {b : σ →₀ ℕ | a ≤ fun i => b i}).comap
    F.positivePolynomialAlgebra.incl.toLinearMap

theorem positivePolynomialMultidegreeLayer_antitone :
    Antitone F.positivePolynomialMultidegreeLayer := by
  intro a b hab p hp c hc
  exact hp c (fun hbc => hc (hab.trans hbc))

theorem positivePolynomialMultidegreeLayer_zero : F.positivePolynomialMultidegreeLayer 0 = ⊤ := by
  apply top_unique
  intro p _ a ha
  exact False.elim (ha (fun i => Nat.zero_le (a i)))

theorem positivePolynomialMultidegreeLayer_lie {a b : σ → ℕ} {p q : F.positivePolynomialAlgebra}
    (hp : p ∈ F.positivePolynomialMultidegreeLayer a)
    (hq : q ∈ F.positivePolynomialMultidegreeLayer b) :
    ⁅p, q⁆ ∈ F.positivePolynomialMultidegreeLayer (a + b) := by
  change ⁅p.val, q.val⁆ ∈ coefficientSupport _
  apply coefficientSupport_lie (S := {c : σ →₀ ℕ | a ≤ fun i => c i})
    (T := {c : σ →₀ ℕ | b ≤ fun i => c i}) _ hp hq
  intro c hc d hd i
  exact add_le_add (hc i) (hd i)

theorem positivePolynomialMultidegreeLayer_terminal (a : σ → ℕ) (ha : ¬a ≤ bound) :
    F.positivePolynomialMultidegreeLayer a = ⊥ := by
  apply bot_unique
  intro p hp
  change p = 0
  apply Subtype.ext
  apply coefficients.injective
  ext b
  change coefficients p.val b = 0
  by_cases hab : a ≤ fun i => b i
  · have hb : ¬(fun i => b i) ≤ bound := fun hb => ha (hab.trans hb)
    simpa only [F.terminal _ hb, Submodule.mem_bot] using p.property.1 b
  · exact hp b hab

theorem positivePolynomialComponent_mem_layer (a : σ →₀ ℕ) (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialComponent a p ∈ F.positivePolynomialMultidegreeLayer (fun i => a i) := by
  change monomial a (coefficients p.val a) ∈
    coefficientSupport {b : σ →₀ ℕ | (fun i => a i) ≤ fun i => b i}
  apply monomial_mem_coefficientSupport
  exact fun i => le_rfl

theorem positivePolynomialDegreeLayer_eq (n : ℕ) :
    F.positivePolynomialDegreeLayer n =
      ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), F.positivePolynomialMultidegreeLayer a := by
  classical
  apply le_antisymm
  · intro p hp
    rw [← F.sum_positivePolynomialComponent p]
    apply Submodule.sum_mem
    intro a ha
    have hn : n ≤ ∑ i, a i := by
      by_contra hn
      exact (Finsupp.mem_support_iff.mp ha) (hp a hn)
    have hle : F.positivePolynomialMultidegreeLayer (fun i => a i) ≤
        ⨆ (b : σ → ℕ) (_hb : n ≤ ∑ i, b i), F.positivePolynomialMultidegreeLayer b :=
      le_iSup_of_le (fun i => a i) (le_iSup_of_le hn le_rfl)
    exact hle (F.positivePolynomialComponent_mem_layer a p)
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha p hp b hb
    apply hp b
    intro hab
    exact hb (ha.trans (Finset.sum_le_sum (fun i _ => hab i)))

noncomputable def positivePolynomialMultidegree :
    MultidegreeLieFiltration σ F.positivePolynomialAlgebra (∑ i, bound i) bound where
  ordinary := F.positivePolynomialDegreeFiltration
  layer := F.positivePolynomialMultidegreeLayer
  antitone := F.positivePolynomialMultidegreeLayer_antitone
  zero_eq_top := F.positivePolynomialMultidegreeLayer_zero
  lie_mem := F.positivePolynomialMultidegreeLayer_lie
  terminal := F.positivePolynomialMultidegreeLayer_terminal
  degree_eq := F.positivePolynomialDegreeLayer_eq

theorem positivePolynomialEvaluation_mem_layer (a : σ → ℕ)
    {p : F.positivePolynomialAlgebra} (hp : p ∈ (F.positivePolynomialMultidegree).layer a) :
    F.positivePolynomialEvaluation p ∈ F.layer a := by
  classical
  rw [F.positivePolynomialEvaluation_apply, ← sum_monomial_coefficients p.val]
  simp only [Finsupp.sum, map_sum, eval_monomial, one_pow, Finsupp.prod,
    Finset.prod_const_one, one_smul]
  apply (F.layer a).sum_mem
  intro b _
  by_cases hab : a ≤ fun i => b i
  · exact F.antitone hab (p.property.1 b)
  · have hz : coefficients p.val b = 0 := hp b hab
    rw [hz]
    exact Submodule.zero_mem _

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {bound : σ → ℕ}

theorem boxedDegreeMonomial_injective : Function.Injective (@boxedDegreeMonomial σ _ bound) := by
  intro a b h
  funext i
  apply Fin.ext
  simpa only [boxedDegreeMonomial_apply] using congrArg (fun c : σ →₀ ℕ => c i) h

theorem boxedDegreeMonomial_le (a : BoxedDegreeIndex bound) :
    (fun i => boxedDegreeMonomial a i) ≤ bound := by
  intro i
  change boxedDegreeMonomial a i ≤ bound i
  rw [boxedDegreeMonomial_apply]
  exact Nat.le_of_lt_succ (a i).isLt

theorem exists_boxedDegreeMonomial (a : σ →₀ ℕ) (ha : (fun i => a i) ≤ bound) :
    ∃ b : BoxedDegreeIndex bound, boxedDegreeMonomial b = a := by
  refine ⟨fun i => ⟨a i, Nat.lt_succ_of_le (ha i)⟩, ?_⟩
  ext i
  exact boxedDegreeMonomial_apply _ i

noncomputable def boxedPolynomial (f : BoxedDegreeIndex bound → L) : VectorPolynomial σ ℚ L := by
  classical
  exact ∑ a, monomial (boxedDegreeMonomial a) (f a)

theorem boxedPolynomial_coefficient (f : BoxedDegreeIndex bound → L) (a : BoxedDegreeIndex bound) :
    coefficients (boxedPolynomial f) (boxedDegreeMonomial a) = f a := by
  classical
  simp [boxedPolynomial, Finsupp.single_apply, boxedDegreeMonomial_injective.eq_iff]

theorem boxedPolynomial_coefficient_outside (f : BoxedDegreeIndex bound → L) (a : σ →₀ ℕ)
    (ha : ¬(fun i => a i) ≤ bound) : coefficients (boxedPolynomial f) a = 0 := by
  classical
  have hne (b : BoxedDegreeIndex bound) : boxedDegreeMonomial b ≠ a := by
    intro h
    apply ha
    simpa only [h] using boxedDegreeMonomial_le b
  simp [boxedPolynomial, hne]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem positivePolynomialComponent_eq_zero (a : σ →₀ ℕ) (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialComponent a p = 0 ↔ coefficients p.val a = 0 := by
  constructor
  · intro h
    have he := congrArg (fun q : F.positivePolynomialAlgebra => coefficients q.val a) h
    change coefficients (monomial a (coefficients p.val a)) a =
      coefficients (0 : VectorPolynomial σ ℚ L) a at he
    simpa only [coefficients_monomial,
      Finsupp.single_eq_same, map_zero, Finsupp.zero_apply] using he
  · intro h
    apply Subtype.ext
    change monomial a (coefficients p.val a) = 0
    simp [h, monomial]

noncomputable def positivePolynomialDiagonal (p : F.positivePolynomialAlgebra) :
    VectorPolynomial σ ℚ F.positivePolynomialAlgebra :=
  (coefficients p.val).sum (fun a _ => monomial a (F.positivePolynomialComponent a p))

theorem positivePolynomialDiagonal_coefficient (p : F.positivePolynomialAlgebra) (a : σ →₀ ℕ) :
    coefficients (F.positivePolynomialDiagonal p) a = F.positivePolynomialComponent a p := by
  classical
  by_cases ha : a ∈ (coefficients p.val).support
  · simp [positivePolynomialDiagonal, Finsupp.sum, Finsupp.single_apply, ha]
  · have hz : F.positivePolynomialComponent a p = 0 :=
      (F.positivePolynomialComponent_eq_zero a p).mpr (Finsupp.notMem_support_iff.mp ha)
    simp [positivePolynomialDiagonal, Finsupp.sum, Finsupp.single_apply, ha, hz]

theorem positivePolynomialDiagonal_adapted (p : F.positivePolynomialAlgebra) :
    F.positivePolynomialMultidegree.Adapted (F.positivePolynomialDiagonal p) := by
  intro a
  rw [F.positivePolynomialDiagonal_coefficient]
  exact F.positivePolynomialComponent_mem_layer a p

theorem positivePolynomialDiagonal_constant (p : F.positivePolynomialAlgebra) :
    coefficients (F.positivePolynomialDiagonal p) 0 = 0 := by
  rw [F.positivePolynomialDiagonal_coefficient, F.positivePolynomialComponent_eq_zero]
  exact p.property.2

theorem positivePolynomialDiagonal_projection (p : F.positivePolynomialAlgebra) :
    VectorPolynomial.map F.positivePolynomialEvaluation.toLinearMap
      (F.positivePolynomialDiagonal p) = p.val := by
  apply coefficients.injective
  ext a
  rw [coefficients_map, F.positivePolynomialDiagonal_coefficient]
  exact F.positivePolynomialEvaluation_component a p

theorem positivePolynomialDiagonal_eval (p : F.positivePolynomialAlgebra) (x : σ → ℚ) :
    F.positivePolynomialEvaluation (eval x (F.positivePolynomialDiagonal p)) = eval x p.val := by
  change F.positivePolynomialEvaluation.toLinearMap (eval x (F.positivePolynomialDiagonal p)) = _
  rw [← eval_map, F.positivePolynomialDiagonal_projection]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem positivePolynomial_support_of_layers (S : Set (σ →₀ ℕ))
    (hS : ∀ a, a ≠ 0 → a ∉ S → F.layer (fun i => a i) = ⊥)
    (p : F.positivePolynomialAlgebra) : p.val ∈ coefficientSupport S := by
  intro a ha
  by_cases hz : a = 0
  · subst a
    exact p.property.2
  · simpa only [hS a hz ha, Submodule.mem_bot] using p.property.1 a

theorem positivePolynomialLayer_le_outsideDownset
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (a : σ →₀ ℕ) (ha : a ∉ J) :
    F.positivePolynomialMultidegreeLayer (fun i => a i) ≤
      (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ).toSubmodule := by
  intro p hp
  apply (mem_restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ p).mpr
  intro b hb
  apply hp b
  intro hab
  exact ha (hJ hab hb)

noncomputable def positivePolynomialDownsetQuotient
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) :=
  F.positivePolynomialMultidegree.quotientMultidegree
    (restrictedOutsideDownsetIdeal F.positivePolynomialAlgebra J hJ)

theorem positivePolynomialDownsetQuotient_terminal
    (J : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (a : σ →₀ ℕ) (ha : a ∉ J) :
    (F.positivePolynomialDownsetQuotient J hJ).layer (fun i => a i) = ⊥ :=
  F.positivePolynomialMultidegree.quotientMultidegree_layer_eq_bot _ _
    (F.positivePolynomialLayer_le_outsideDownset J hJ a ha)

theorem positivePolynomial_downset_pair_injective
    (J K : Set (σ →₀ ℕ)) (hJ : IsLowerSet J) (hK : IsLowerSet K)
    (hcover : ∀ a, a ≠ 0 → a ∉ J ∪ K → F.layer (fun i => a i) = ⊥) :
    Function.Injective (downsetPairQuotientMap F.positivePolynomialAlgebra J K hJ hK) :=
  downsetPairQuotientMap_injective F.positivePolynomialAlgebra J K hJ hK
    (F.positivePolynomial_support_of_layers (J ∪ K) hcover)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_positivePolynomial_orbit (g : F.PolynomialOrbit)
    (hg : F.polynomialOrbitEval 0 g = 1) :
    ∃ h : F.positivePolynomialMultidegree.PolynomialOrbit,
      F.positivePolynomialMultidegree.polynomialOrbitEval 0 h = 1 ∧
      ∀ x, NilpotentLieBCHGroup.mapOfSteps F.positivePolynomialEvaluation
          (F.positivePolynomialMultidegree.polynomialOrbitEval x h) =
        F.polynomialOrbitEval x g := by
  have hzero : coefficients (PolynomialOrbit.log F g) 0 = 0 := by
    have hcoord := congrArg NilpotentLieBCHGroup.coord hg
    change eval (fun i => ((0 : σ → ℤ) i : ℚ)) (PolynomialOrbit.log F g) = 0 at hcoord
    simpa only [Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using hcoord
  let p : F.positivePolynomialAlgebra := ⟨PolynomialOrbit.log F g, PolynomialOrbit.adapted F g, hzero⟩
  let h := F.positivePolynomialMultidegree.polynomialOrbitOfLog
    (F.positivePolynomialDiagonal p) (F.positivePolynomialDiagonal_adapted p)
  refine ⟨h, ?_, ?_⟩
  · apply NilpotentLieBCHGroup.ext
    change eval (fun i => ((0 : σ → ℤ) i : ℚ)) (F.positivePolynomialDiagonal p) = 0
    simpa only [Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using
      F.positivePolynomialDiagonal_constant p
  · intro x
    apply NilpotentLieBCHGroup.ext
    exact F.positivePolynomialDiagonal_eval p (fun i => (x i : ℚ))

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realPositivePolynomialEvaluation_commute (x : ℝ ⊗[ℚ] F.positivePolynomialAlgebra) :
    F.realification.positivePolynomialEvaluation (F.realPositivePolynomialTensor x) =
      realificationLieHom F.positivePolynomialEvaluation x := by
  induction x using TensorProduct.inductionOn with
  | tmul r p =>
    change eval (fun _ : σ => (1 : ℚ))
      (VectorPolynomial.realificationLieEquiv (r ⊗ₜ[ℚ] p.val)) =
        r ⊗ₜ[ℚ] eval (fun _ : σ => (1 : ℚ)) p.val
    exact eval_realificationLieEquiv_tmul r p.val _
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.MultidegreeLieFiltration

end

end OAI
