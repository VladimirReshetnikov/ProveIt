/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.MvPolynomial
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Binomial
import OAI.Combinatorics.Progressions.Linear.FiniteSpanSum
import OAI.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth
import OAI.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
import OAI.Combinatorics.Progressions.Polynomial.BinomialPolynomial
import OAI.Combinatorics.Progressions.Polynomial.PolynomialSmooth

namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialSupportBox (α : σ →₀ ℕ) : Submodule R (MvPolynomial σ R) where
  carrier := {p | ∀ β ∈ p.support, β ≤ α}
  zero_mem' := by simp
  add_mem' hp hq := by
    classical
    intro β hβ
    rcases Finset.mem_union.mp (MvPolynomial.support_add hβ) with h | h
    · exact hp β h
    · exact hq β h
  smul_mem' c p hp := by
    intro β hβ
    exact hp β (MvPolynomial.support_smul hβ)

theorem monomial_mem_polynomialSupportBox {α β : σ →₀ ℕ} (hβα : β ≤ α) (c : R) :
    MvPolynomial.monomial β c ∈ polynomialSupportBox α := by
  classical
  intro γ hγ
  have h : γ = β := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hγ)
  simpa only [h] using hβα

theorem polynomialSupportBox_mono {α β : σ →₀ ℕ} (hαβ : α ≤ β) :
    polynomialSupportBox (R := R) α ≤ polynomialSupportBox β :=
  fun _ hp γ hγ => (hp γ hγ).trans hαβ

theorem mul_mem_polynomialSupportBox {α β : σ →₀ ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ polynomialSupportBox α) (hq : q ∈ polynomialSupportBox β) :
    p * q ∈ polynomialSupportBox (α + β) := by
  classical
  intro γ hγ
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hγ)
  exact add_le_add (hp a ha) (hq b hb)

theorem prod_mem_polynomialSupportBox {κ : Type*} (u : Finset κ)
    (α : κ → σ →₀ ℕ) (p : κ → MvPolynomial σ R)
    (hp : ∀ i ∈ u, p i ∈ polynomialSupportBox (α i)) :
    (∏ i ∈ u, p i) ∈ polynomialSupportBox (∑ i ∈ u, α i) := by
  classical
  induction u using Finset.induction_on with
  | empty =>
    change MvPolynomial.monomial 0 (1 : R) ∈ polynomialSupportBox 0
    exact monomial_mem_polynomialSupportBox le_rfl 1
  | @insert i u hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_polynomialSupportBox (hp i (Finset.mem_insert_self ..))
      (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem finsupp_weight_mono (w : σ → ℕ) {α β : σ →₀ ℕ} (h : α ≤ β) :
    Finsupp.weight w α ≤ Finsupp.weight w β := by
  obtain ⟨γ, rfl⟩ := exists_add_of_le h
  rw [map_add]
  exact Nat.le_add_right _ _

theorem weightedDegree_le_of_mem_polynomialSupportBox (w : σ → ℕ)
    {α : σ →₀ ℕ} {p : MvPolynomial σ R} (hp : p ∈ polynomialSupportBox α) :
    p.weightedTotalDegree w ≤ Finsupp.weight w α := by
  classical
  rw [MvPolynomial.weightedTotalDegree, Finset.sup_le_iff]
  exact fun β hβ => finsupp_weight_mono w (hp β hβ)

theorem polynomial_aeval_X_mem_supportBox (i : σ) (p : Polynomial R) {n : ℕ}
    (hp : p.natDegree ≤ n) :
    Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ R) p ∈
      polynomialSupportBox (Finsupp.single i n) := by
  classical
  rw [Polynomial.aeval_eq_sum_range]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  rw [MvPolynomial.X_pow_eq_monomial]
  apply monomial_mem_polynomialSupportBox
  have hkn : k ≤ n := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hp
  intro j
  by_cases h : i = j
  · subst j
    simpa using hkn
  · simp [h]

end Erdos3

end

section

namespace Erdos3

variable {σ : Type*}

noncomputable def binomialVariable (i : σ) (n : ℕ) : MvPolynomial σ ℚ :=
  Polynomial.aeval (MvPolynomial.X i) (binomialPolynomial n)

@[simp] theorem binomialVariable_zero (i : σ) : binomialVariable i 0 = 1 := by
  simp [binomialVariable]

noncomputable def multivariateBinomial (α : σ →₀ ℕ) : MvPolynomial σ ℚ :=
  α.prod binomialVariable

@[simp] theorem multivariateBinomial_zero : multivariateBinomial (0 : σ →₀ ℕ) = 1 := by
  simp [multivariateBinomial]

@[simp] theorem multivariateBinomial_single (i : σ) (n : ℕ) :
    multivariateBinomial (Finsupp.single i n) = binomialVariable i n := by
  classical
  simp [multivariateBinomial]

theorem multivariateBinomial_add_of_disjoint {α β : σ →₀ ℕ}
    (h : Disjoint α.support β.support) :
    multivariateBinomial (α + β) = multivariateBinomial α * multivariateBinomial β :=
  Finsupp.prod_add_index_of_disjoint h _

theorem binomialVariable_mem_supportBox (i : σ) (n : ℕ) :
    binomialVariable i n ∈ polynomialSupportBox (Finsupp.single i n) :=
  polynomial_aeval_X_mem_supportBox i _ (le_of_eq (binomialPolynomial_natDegree n))

theorem multivariateBinomial_mem_supportBox (α : σ →₀ ℕ) :
    multivariateBinomial α ∈ polynomialSupportBox α := by
  have h := prod_mem_polynomialSupportBox α.support (fun i => Finsupp.single i (α i))
    (fun i => binomialVariable i (α i)) (fun i _ => binomialVariable_mem_supportBox i (α i))
  have heq : (∑ i ∈ α.support, Finsupp.single i (α i)) = α := Finsupp.sum_single α
  simpa only [heq, multivariateBinomial, Finsupp.prod] using h

theorem multivariateBinomial_weightedDegree (w : σ → ℕ) (α : σ →₀ ℕ) :
    (multivariateBinomial α).weightedTotalDegree w ≤ Finsupp.weight w α :=
  weightedDegree_le_of_mem_polynomialSupportBox w (multivariateBinomial_mem_supportBox α)

theorem binomialVariable_eval_nat (i : σ) (n : ℕ) (x : σ → ℕ) :
    MvPolynomial.aeval (fun j => (x j : ℚ)) (binomialVariable i n) = (Nat.choose (x i) n : ℚ) := by
  rw [binomialVariable, ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]
  exact binomialPolynomial_eval_nat n (x i)

theorem multivariateBinomial_eval_nat (α : σ →₀ ℕ) (x : σ → ℕ) :
    MvPolynomial.aeval (fun j => (x j : ℚ)) (multivariateBinomial α) =
      α.prod (fun i n => (Nat.choose (x i) n : ℚ)) := by
  simp only [multivariateBinomial, Finsupp.prod, map_prod, binomialVariable_eval_nat]

end Erdos3

end

section

namespace Erdos3

open Polynomial

theorem binomialPolynomial_aeval_choose {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (n : ℕ) (x : K) : Polynomial.aeval x (binomialPolynomial n) = Ring.choose x n := by
  have hq : Polynomial.aeval x (descPochhammer ℚ n) = (descPochhammer K n).eval x := by
    rw [← descPochhammer_map (algebraMap ℚ K) n, eval_map]
    rfl
  have hz : (descPochhammer ℤ n).smeval x = (descPochhammer K n).eval x := by
    rw [← aeval_eq_smeval, ← descPochhammer_map (algebraMap ℤ K) n, eval_map]
    rfl
  simp only [binomialPolynomial, smul_eq_C_mul, map_mul, aeval_C, map_inv₀, map_natCast,
    hq, Ring.choose_eq_smul, hz, smul_eq_mul]

theorem binomialPolynomial_eval_int (n : ℕ) (x : ℤ) :
    (binomialPolynomial n).eval (x : ℚ) = (Ring.choose x n : ℤ) := by
  change Polynomial.aeval (x : ℚ) (binomialPolynomial n) = _
  rw [binomialPolynomial_aeval_choose n (x : ℚ)]
  exact (Ring.map_choose (Int.castRingHom ℚ) x n).symm

theorem multivariateBinomial_aeval_choose {σ K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
    (α : σ →₀ ℕ) (x : σ → K) :
    MvPolynomial.aeval x (multivariateBinomial α) = α.prod (fun i n => Ring.choose (x i) n) := by
  simp only [multivariateBinomial, Finsupp.prod, map_prod, binomialVariable,
    ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X, binomialPolynomial_aeval_choose]

theorem multivariateBinomial_eval_int {σ : Type*} (α : σ →₀ ℕ) (x : σ → ℤ) :
    MvPolynomial.aeval (fun i => (x i : ℚ)) (multivariateBinomial α) =
      α.prod (fun i n => ((Ring.choose (x i) n : ℤ) : ℚ)) := by
  rw [multivariateBinomial_aeval_choose α (fun i => (x i : ℚ))]
  apply Finsupp.prod_congr
  intro i _
  exact (Ring.map_choose (Int.castRingHom ℚ) (x i) (α i)).symm

end Erdos3

end

section

namespace Erdos3

open scoped Pointwise

variable {σ : Type*}

noncomputable def binomialSpan (α : σ →₀ ℕ) : Submodule ℚ (MvPolynomial σ ℚ) :=
  Submodule.span ℚ (multivariateBinomial '' Set.Iic α)

theorem multivariateBinomial_mem_binomialSpan {α β : σ →₀ ℕ} (h : β ≤ α) :
    multivariateBinomial β ∈ binomialSpan α :=
  Submodule.subset_span ⟨β, h, rfl⟩

theorem binomialSpan_mono {α β : σ →₀ ℕ} (h : α ≤ β) : binomialSpan α ≤ binomialSpan β :=
  Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.mpr h))

theorem mul_mem_binomialSpan_of_disjoint {α β : σ →₀ ℕ}
    (h : Disjoint α.support β.support) {p q : MvPolynomial σ ℚ}
    (hp : p ∈ binomialSpan α) (hq : q ∈ binomialSpan β) : p * q ∈ binomialSpan (α + β) := by
  have hle : binomialSpan α * binomialSpan β ≤ binomialSpan (α + β) := by
    unfold binomialSpan
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    change a ≤ α at ha
    change b ≤ β at hb
    dsimp only
    rw [← multivariateBinomial_add_of_disjoint
      (h.mono (Finsupp.support_mono ha) (Finsupp.support_mono hb))]
    refine Submodule.subset_span ⟨a + b, ?_, rfl⟩
    change a + b ≤ α + β
    exact add_le_add ha hb
  exact hle (Submodule.mul_mem_mul hp hq)

theorem monomial_single_mem_binomialSpan (i : σ) (n : ℕ) :
    MvPolynomial.monomial (Finsupp.single i n) (1 : ℚ) ∈ binomialSpan (Finsupp.single i n) := by
  have h : (MvPolynomial.X i : MvPolynomial σ ℚ) ^ n =
      ∑ k ∈ Finset.range (n + 1), ((Nat.stirlingSecond n k * k.factorial : ℕ) : ℚ) •
        binomialVariable i k := by
    simpa only [map_pow, Polynomial.aeval_X, map_sum, map_smul, binomialVariable] using
      congrArg (Polynomial.aeval (MvPolynomial.X i : MvPolynomial σ ℚ))
        (X_pow_eq_sum_binomialPolynomial n)
  rw [← MvPolynomial.X_pow_eq_monomial, h]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  rw [← multivariateBinomial_single]
  exact multivariateBinomial_mem_binomialSpan
    (Finsupp.single_le_single.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

theorem monomial_mem_binomialSpan (α : σ →₀ ℕ) :
    MvPolynomial.monomial α (1 : ℚ) ∈ binomialSpan α := by
  classical
  induction α using Finsupp.induction with
  | zero =>
    simpa only [multivariateBinomial_zero, MvPolynomial.one_def] using
      multivariateBinomial_mem_binomialSpan (α := (0 : σ →₀ ℕ)) le_rfl
  | @single_add i n α hi hn ih =>
    have heq : MvPolynomial.monomial (Finsupp.single i n + α) (1 : ℚ) =
        MvPolynomial.monomial (Finsupp.single i n) 1 * MvPolynomial.monomial α 1 := by
      rw [MvPolynomial.monomial_mul_monomial, one_mul]
    rw [heq]
    apply mul_mem_binomialSpan_of_disjoint _ (monomial_single_mem_binomialSpan i n) ih
    simpa only [Finsupp.support_single i hn, Finset.disjoint_singleton_left] using hi

theorem binomialSpan_eq_supportBox (α : σ →₀ ℕ) :
    binomialSpan α = polynomialSupportBox α := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨β, hβ, rfl⟩
    exact polynomialSupportBox_mono hβ (multivariateBinomial_mem_supportBox β)
  · intro p hp
    rw [MvPolynomial.as_sum p]
    apply Submodule.sum_mem
    intro β hβ
    have h := (binomialSpan α).smul_mem (p.coeff β)
      (binomialSpan_mono (hp β hβ) (monomial_mem_binomialSpan β))
    simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using h

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial Module
open scoped Manifold ContDiff TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} (F : NilpotentLieFiltration L s)

noncomputable def polynomialOrbitRealEval (w : σ → ℕ) (x : σ → ℝ) :
    F.PolynomialOrbit w →* F.Group :=
  (NilpotentLieBCHGroup.map (eval₂Lie (R := ℚ) (L := L) x)).comp
    (F.polynomialSubgroup w).subtype

@[simp] theorem polynomialOrbitRealEval_coord (w : σ → ℕ)
    (p : F.PolynomialOrbit w) (x : σ → ℝ) :
    (F.polynomialOrbitRealEval w x p).coord = eval₂ x p.log := rfl

theorem polynomialOrbitRealEval_integer (w : σ → ℕ) (p : F.PolynomialOrbit w)
    (x : σ → ℤ) :
    F.polynomialOrbitRealEval w (fun i => (x i : ℝ)) p = F.polynomialOrbitEval w x p := by
  apply NilpotentLieBCHGroup.ext
  simpa only [polynomialOrbitRealEval_coord, polynomialOrbitEval_coord,
    map_intCast] using
    eval₂_algebraMap (S := ℝ) (fun i => (x i : ℚ)) p.log

theorem polynomialOrbitRealEval_coordinates [Fintype ι] (e : Basis ι ℝ L)
    (w : σ → ℕ) (p : F.PolynomialOrbit w) (x : σ → ℝ) :
    e.equivFun (F.polynomialOrbitRealEval w x p).coord =
      fun i => MvPolynomial.eval x (coordinate (e.coord i).toAddMonoidHom p.log) := by
  funext i
  exact coordinate_eval₂ (e.coord i) x p.log

section Smooth

variable [Fintype ι] [Fintype σ] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]

theorem contMDiff_polynomialOrbitRealEval (e : Basis ι ℝ L) (w : σ → ℕ)
    (p : F.PolynomialOrbit w) (n : ℕ∞ω) :
    letI := NilpotentLieBCHGroup.basisChartedSpace (hnil := F.lowerCentralSeries_eq_bot) e
    ContMDiff 𝓘(ℝ, σ → ℝ) 𝓘(ℝ, ι → ℝ) n (fun x => F.polynomialOrbitRealEval w x p) := by
  let := NilpotentLieBCHGroup.basisChartedSpace (hnil := F.lowerCentralSeries_eq_bot) e
  apply ContMDiff.of_comp_isOpenEmbedding
    (NilpotentLieBCHGroup.basisHomeomorph e).isOpenEmbedding
  have hp : ContDiff ℝ n (fun x : σ → ℝ => fun i =>
      MvPolynomial.eval x (coordinate (e.coord i).toAddMonoidHom p.log)) := by
    apply contDiff_pi.mpr
    intro i
    simpa only [MvPolynomial.aeval_eq_eval] using
      contDiff_mvPolynomial (coordinate (e.coord i).toAddMonoidHom p.log) n
  simpa only [Function.comp_def, NilpotentLieBCHGroup.basisHomeomorph_apply,
    polynomialOrbitRealEval_coordinates] using hp.contMDiff

end Smooth
end Erdos3.NilpotentLieFiltration

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial Module
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem real_adapted_iff_quotient_coordinates {κ : ℕ → Type*}
    (e : ∀ i, Basis (κ i) ℝ ((ℝ ⊗[ℚ] L) ⧸ (F.realLayer (i + 1)).toSubmodule))
    (w : σ → ℕ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    F.realification.Adapted w p ↔ ∀ i j,
      (coordinate ((e i).coord j).toAddMonoidHom
        (VectorPolynomial.map ((F.realLayer (i + 1)).toSubmodule.mkQ.restrictScalars ℚ) p)).weightedTotalDegree w ≤ i := by
  unfold Adapted
  apply forall_congr'
  intro i
  exact degreeLE_iff_basis_coordinates (e i) w i _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

structure AdaptedMonomial (w : σ → ℕ) where
  exponent : σ →₀ ℕ
  coefficient : L
  coefficient_mem : coefficient ∈ F.layer (Finsupp.weight w exponent)

namespace AdaptedMonomial

variable {F} {w : σ → ℕ}

noncomputable def logarithm (u : F.AdaptedMonomial w) : F.adaptedLieSubalgebra w :=
  ⟨monomial u.exponent u.coefficient,
    F.monomial_mem_adaptedSubmodule w u.exponent u.coefficient_mem⟩

@[simp] theorem coe_logarithm (u : F.AdaptedMonomial w) :
    (u.logarithm : VectorPolynomial σ ℚ L) = monomial u.exponent u.coefficient := rfl

end AdaptedMonomial

noncomputable def adaptedBCHToOrbit (w : σ → ℕ) :
    (F.adaptedPolynomialFiltration w).Group →* F.PolynomialOrbit w :=
  (NilpotentLieBCHGroup.map (hnil := (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot)
    (hM := VectorPolynomial.lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot)
    (F.adaptedLieSubalgebra w).incl).codRestrict _ (fun g => g.coord.property)

namespace AdaptedMonomial

variable {F} {w : σ → ℕ}

noncomputable def orbit (u : F.AdaptedMonomial w) : F.PolynomialOrbit w :=
  F.adaptedBCHToOrbit w ⟨u.logarithm⟩

@[simp] theorem orbit_log (u : F.AdaptedMonomial w) :
    u.orbit.log = monomial u.exponent u.coefficient := rfl

theorem eval_coord (u : F.AdaptedMonomial w) (x : σ → ℤ) :
    (F.polynomialOrbitEval w x u.orbit).coord =
      (u.exponent.prod fun i n => (x i : ℚ) ^ n) • u.coefficient := by
  rw [polynomialOrbitEval_coord, orbit_log, eval_monomial]

end AdaptedMonomial

theorem exists_layerwise_monomial_sum (w : σ → ℕ) (i : ℕ)
    (p : F.adaptedLieSubalgebra w) (hp : p ∈ (F.adaptedPolynomialFiltration w).layer i) :
    ∃ xs : List (F.adaptedLieSubalgebra w),
      (∀ q ∈ xs, q ∈ Set.range (AdaptedMonomial.logarithm (F := F) (w := w)) ∧
        q ∈ (F.adaptedPolynomialFiltration w).layer i) ∧ xs.sum = p := by
  classical
  let m (α : σ →₀ ℕ) : F.AdaptedMonomial w :=
    ⟨α, coefficients (p : VectorPolynomial σ ℚ L) α, p.property α⟩
  let xs := (coefficients (p : VectorPolynomial σ ℚ L)).support.toList.map
    (fun α => (m α).logarithm)
  refine ⟨xs, ?_, ?_⟩
  · intro q hq
    obtain ⟨α, _, rfl⟩ := List.mem_map.mp hq
    refine ⟨⟨m α, rfl⟩, ?_⟩
    change monomial α (coefficients (p : VectorPolynomial σ ℚ L) α) ∈ F.polynomialLayer i
    exact F.monomial_mem_polynomialLayer i α (hp α)
  · apply Subtype.val_injective
    change (F.adaptedLieSubalgebra w).incl xs.sum = (p : VectorPolynomial σ ℚ L)
    rw [map_list_sum]
    simp only [xs, List.map_map, Function.comp_def]
    change ((coefficients (p : VectorPolynomial σ ℚ L)).support.toList.map
      (fun α => monomial (R := ℚ) α (coefficients (p : VectorPolynomial σ ℚ L) α))).sum = _
    rw [Finset.sum_map_toList]
    exact sum_monomial_coefficients _

theorem exists_monomial_factorization (w : σ → ℕ) (p : F.PolynomialOrbit w) :
    ∃ xs : List (F.AdaptedMonomial w), (xs.map AdaptedMonomial.orbit).prod = p := by
  let a : F.adaptedLieSubalgebra w := ⟨p.log, p.property⟩
  obtain ⟨xs, hxs⟩ := (F.adaptedPolynomialFiltration w).exists_product_of_layerwise_range
    AdaptedMonomial.logarithm (fun i _ q hq => F.exists_layerwise_monomial_sum w i q hq) a
  refine ⟨xs, ?_⟩
  have h := congrArg (F.adaptedBCHToOrbit w) hxs
  rw [map_list_prod] at h
  have ha : F.adaptedBCHToOrbit w ⟨a⟩ = p := by
    apply Subtype.val_injective
    apply NilpotentLieBCHGroup.ext
    rfl
  rw [ha] at h
  change (xs.map (fun u => F.adaptedBCHToOrbit w ⟨u.logarithm⟩)).prod = p
  simpa only [List.map_map, Function.comp_def] using h

theorem exists_monomial_factorization_eval (w : σ → ℕ) (p : F.PolynomialOrbit w) :
    ∃ xs : List (F.AdaptedMonomial w), ∀ x : σ → ℤ,
      (xs.map (fun u => F.polynomialOrbitEval w x u.orbit)).prod = F.polynomialOrbitEval w x p := by
  obtain ⟨xs, hxs⟩ := F.exists_monomial_factorization w p
  refine ⟨xs, fun x => ?_⟩
  have h := congrArg (F.polynomialOrbitEval w x) hxs
  simpa only [map_list_prod, List.map_map, Function.comp_def] using h

section Real

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

theorem AdaptedMonomial.evalReal_coord {F : NilpotentLieFiltration L s} {w : σ → ℕ}
    (u : F.AdaptedMonomial w) (x : σ → ℝ) :
    (F.polynomialOrbitRealEval w x u.orbit).coord =
      (u.exponent.prod fun i n => x i ^ n) • u.coefficient := by
  rw [polynomialOrbitRealEval_coord, AdaptedMonomial.orbit_log, eval₂_monomial]

theorem exists_monomial_factorization_evalReal (w : σ → ℕ) (p : F.PolynomialOrbit w) :
    ∃ xs : List (F.AdaptedMonomial w), ∀ x : σ → ℝ,
      (xs.map (fun u => F.polynomialOrbitRealEval w x u.orbit)).prod =
        F.polynomialOrbitRealEval w x p := by
  obtain ⟨xs, hxs⟩ := F.exists_monomial_factorization w p
  refine ⟨xs, fun x => ?_⟩
  have h := congrArg (F.polynomialOrbitRealEval w x) hxs
  simpa only [map_list_prod, List.map_map, Function.comp_def] using h

end Real

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F G : NilpotentLieFiltration L s) (hGF : G = F) (w : σ → ℕ)

noncomputable def realPolynomialOrbitChangeFiltration
    (orbit : F.realification.PolynomialOrbit w) : G.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog orbit.log (by rw [hGF]; exact orbit.adapted)

@[simp] theorem realPolynomialOrbitChangeFiltration_log
    (orbit : F.realification.PolynomialOrbit w) :
    (F.realPolynomialOrbitChangeFiltration G hGF w orbit).log = orbit.log := rfl

theorem realPolynomialOrbitChangeFiltration_realEval
    (orbit : F.realification.PolynomialOrbit w) (t : σ → ℝ) :
    G.realification.polynomialOrbitRealEval w t
      (F.realPolynomialOrbitChangeFiltration G hGF w orbit) =
        F.realification.polynomialOrbitRealEval w t orbit := by
  apply NilpotentLieBCHGroup.ext
  rfl

theorem realPolynomialOrbitChangeFiltration_eval
    (orbit : F.realification.PolynomialOrbit w) (t : σ → ℤ) :
    G.realification.polynomialOrbitEval w t
      (F.realPolynomialOrbitChangeFiltration G hGF w orbit) =
        F.realification.polynomialOrbitEval w t orbit := by
  apply NilpotentLieBCHGroup.ext
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem tensor_adapted_of_supportBox (w : σ → ℕ) {α : σ →₀ ℕ}
    {q : MvPolynomial σ ℚ} (hq : q ∈ polynomialSupportBox α) {a : L}
    (ha : a ∈ F.layer (Finsupp.weight w α)) : F.Adapted w (q ⊗ₜ[ℚ] a) := by
  apply (F.adapted_iff_coefficients w _).mpr
  intro β
  rw [coefficients_tmul]
  by_cases hc : q.coeff β = 0
  · simp [hc]
  · apply Submodule.smul_mem
    exact F.antitone (finsupp_weight_mono w (hq β (MvPolynomial.mem_support_iff.mpr hc))) ha

theorem tensor_mem_polynomialLayer (i : ℕ) (q : MvPolynomial σ ℚ) {a : L}
    (ha : a ∈ F.layer i) : q ⊗ₜ[ℚ] a ∈ F.polynomialLayer i := by
  intro β
  rw [coefficients_tmul]
  exact (F.layer i).smul_mem _ ha

structure AdaptedBinomial (w : σ → ℕ) where
  exponent : σ →₀ ℕ
  coefficient : L
  coefficient_mem : coefficient ∈ F.layer (Finsupp.weight w exponent)

namespace AdaptedBinomial

variable {F} {w : σ → ℕ}

noncomputable def logarithm (u : F.AdaptedBinomial w) : F.adaptedLieSubalgebra w :=
  ⟨multivariateBinomial u.exponent ⊗ₜ[ℚ] u.coefficient,
    (F.mem_adaptedSubmodule w _).mpr
      (F.tensor_adapted_of_supportBox w (multivariateBinomial_mem_supportBox u.exponent)
        u.coefficient_mem)⟩

@[simp] theorem coe_logarithm (u : F.AdaptedBinomial w) :
    (u.logarithm : VectorPolynomial σ ℚ L) =
      multivariateBinomial u.exponent ⊗ₜ[ℚ] u.coefficient := rfl

def scale (c : ℚ) (u : F.AdaptedBinomial w) : F.AdaptedBinomial w where
  exponent := u.exponent
  coefficient := c • u.coefficient
  coefficient_mem := (F.layer _).smul_mem c u.coefficient_mem

theorem logarithm_scale (c : ℚ) (u : F.AdaptedBinomial w) :
    (u.scale c).logarithm = c • u.logarithm := by
  apply Subtype.val_injective
  change multivariateBinomial u.exponent ⊗ₜ[ℚ] (c • u.coefficient) =
    c • (multivariateBinomial u.exponent ⊗ₜ[ℚ] u.coefficient)
  simp only [TensorProduct.tmul_smul]

theorem logarithm_mem_layer (u : F.AdaptedBinomial w) {i : ℕ}
    (hi : u.coefficient ∈ F.layer i) :
    u.logarithm ∈ (F.adaptedPolynomialFiltration w).layer i :=
  F.tensor_mem_polynomialLayer i _ hi

noncomputable def orbit (u : F.AdaptedBinomial w) : F.PolynomialOrbit w :=
  F.adaptedBCHToOrbit w ⟨u.logarithm⟩

@[simp] theorem orbit_log (u : F.AdaptedBinomial w) :
    u.orbit.log = multivariateBinomial u.exponent ⊗ₜ[ℚ] u.coefficient := rfl

end AdaptedBinomial
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def binomialLayerGenerators (w : σ → ℕ) (i : ℕ) : Set (VectorPolynomial σ ℚ L) :=
  {q | ∃ u : F.AdaptedBinomial w, u.coefficient ∈ F.layer i ∧ (u.logarithm : VectorPolynomial σ ℚ L) = q}

theorem smul_mem_binomialLayerGenerators (w : σ → ℕ) (i : ℕ) (c : ℚ)
    {p : VectorPolynomial σ ℚ L} (hp : p ∈ F.binomialLayerGenerators w i) :
    c • p ∈ F.binomialLayerGenerators w i := by
  obtain ⟨u, hu, rfl⟩ := hp
  refine ⟨u.scale c, (F.layer i).smul_mem c hu, ?_⟩
  exact congrArg (fun q : F.adaptedLieSubalgebra w => (q : VectorPolynomial σ ℚ L))
    (u.logarithm_scale c)

theorem monomial_mem_binomialLayerSpan (w : σ → ℕ) (i : ℕ) (α : σ →₀ ℕ) {a : L}
    (ha : a ∈ F.layer (Finsupp.weight w α)) (hai : a ∈ F.layer i) :
    monomial (R := ℚ) α a ∈ Submodule.span ℚ (F.binomialLayerGenerators w i) := by
  let φ : MvPolynomial σ ℚ →ₗ[ℚ] VectorPolynomial σ ℚ L :=
    (TensorProduct.mk ℚ (MvPolynomial σ ℚ) L).flip a
  have hle : binomialSpan α ≤ (Submodule.span ℚ (F.binomialLayerGenerators w i)).comap φ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨β, hβ, rfl⟩
    change φ (multivariateBinomial β) ∈ Submodule.span ℚ (F.binomialLayerGenerators w i)
    apply Submodule.subset_span
    exact ⟨⟨β, a, F.antitone (finsupp_weight_mono w hβ) ha⟩, hai, rfl⟩
  exact hle (monomial_mem_binomialSpan α)

theorem adapted_mem_binomialLayerSpan (w : σ → ℕ) (i : ℕ)
    (p : F.adaptedLieSubalgebra w) (hp : p ∈ (F.adaptedPolynomialFiltration w).layer i) :
    (p : VectorPolynomial σ ℚ L) ∈ Submodule.span ℚ (F.binomialLayerGenerators w i) := by
  rw [← sum_monomial_coefficients (p : VectorPolynomial σ ℚ L)]
  simp only [Finsupp.sum]
  apply Submodule.sum_mem
  intro α _
  exact F.monomial_mem_binomialLayerSpan w i α (p.property α) (hp α)

theorem exists_layerwise_binomial_sum (w : σ → ℕ) (i : ℕ)
    (p : F.adaptedLieSubalgebra w) (hp : p ∈ (F.adaptedPolynomialFiltration w).layer i) :
    ∃ xs : List (F.adaptedLieSubalgebra w),
      (∀ q ∈ xs, q ∈ Set.range (AdaptedBinomial.logarithm (F := F) (w := w)) ∧
        q ∈ (F.adaptedPolynomialFiltration w).layer i) ∧ xs.sum = p := by
  classical
  obtain ⟨ys, hys, hy⟩ := exists_list_sum_of_mem_span (F.binomialLayerGenerators w i)
    (fun c _ h => F.smul_mem_binomialLayerGenerators w i c h)
    (F.adapted_mem_binomialLayerSpan w i p hp)
  have hgen (y : {q : VectorPolynomial σ ℚ L // q ∈ ys}) :
      ∃ u : F.AdaptedBinomial w, u.coefficient ∈ F.layer i ∧
        (u.logarithm : VectorPolynomial σ ℚ L) = y.val := hys y.val y.property
  choose u hu using hgen
  let xs := ys.attach.map (fun y => (u y).logarithm)
  refine ⟨xs, ?_, ?_⟩
  · intro q hq
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hq
    exact ⟨⟨u y, rfl⟩, (u y).logarithm_mem_layer (hu y).1⟩
  · apply Subtype.val_injective
    change (F.adaptedLieSubalgebra w).incl xs.sum = (p : VectorPolynomial σ ℚ L)
    rw [map_list_sum]
    simp only [xs, List.map_map, Function.comp_def]
    have hfun : (fun y : {q : VectorPolynomial σ ℚ L // q ∈ ys} =>
        (F.adaptedLieSubalgebra w).incl (u y).logarithm) = Subtype.val :=
      funext (fun y => (hu y).2)
    rw [hfun, List.attach_map_subtype_val, hy]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem exists_binomial_factorization (w : σ → ℕ) (p : F.PolynomialOrbit w) :
    ∃ xs : List (F.AdaptedBinomial w), (xs.map AdaptedBinomial.orbit).prod = p := by
  let a : F.adaptedLieSubalgebra w := ⟨p.log, p.property⟩
  obtain ⟨xs, hxs⟩ := (F.adaptedPolynomialFiltration w).exists_product_of_layerwise_range
    AdaptedBinomial.logarithm (fun i _ q hq => F.exists_layerwise_binomial_sum w i q hq) a
  refine ⟨xs, ?_⟩
  have h := congrArg (F.adaptedBCHToOrbit w) hxs
  rw [map_list_prod] at h
  have ha : F.adaptedBCHToOrbit w ⟨a⟩ = p := by
    apply Subtype.val_injective
    apply NilpotentLieBCHGroup.ext
    rfl
  rw [ha] at h
  change (xs.map (fun u => F.adaptedBCHToOrbit w ⟨u.logarithm⟩)).prod = p
  simpa only [List.map_map, Function.comp_def] using h

theorem adapted_iff_binomial_factorization (w : σ → ℕ) (p : VectorPolynomial σ ℚ L) :
    F.Adapted w p ↔ ∃ xs : List (F.AdaptedBinomial w),
      ((xs.map AdaptedBinomial.orbit).prod).log = p := by
  constructor
  · intro hp
    obtain ⟨xs, hxs⟩ := F.exists_binomial_factorization w (polynomialOrbitOfLog p hp)
    exact ⟨xs, congrArg PolynomialOrbit.log hxs⟩
  · rintro ⟨xs, hxs⟩
    rw [← hxs]
    exact ((xs.map AdaptedBinomial.orbit).prod).adapted

theorem AdaptedBinomial.eval_coord {F : NilpotentLieFiltration L s} {w : σ → ℕ}
    (u : F.AdaptedBinomial w) (x : σ → ℤ) :
    (F.polynomialOrbitEval w x u.orbit).coord =
      MvPolynomial.aeval (fun i => (x i : ℚ)) (multivariateBinomial u.exponent) • u.coefficient := by
  rw [polynomialOrbitEval_coord, AdaptedBinomial.orbit_log, eval_tmul]

theorem AdaptedBinomial.eval_eq_choose {F : NilpotentLieFiltration L s} {w : σ → ℕ}
    (u : F.AdaptedBinomial w) (x : σ → ℤ) :
    F.polynomialOrbitEval w x u.orbit =
      (⟨(u.exponent.prod fun i n => ((Ring.choose (x i) n : ℤ) : ℚ)) • u.coefficient⟩ : F.Group) := by
  apply NilpotentLieBCHGroup.ext
  rw [u.eval_coord, multivariateBinomial_eval_int]

theorem exists_binomial_factorization_eval (w : σ → ℕ) (p : F.PolynomialOrbit w) :
    ∃ xs : List (F.AdaptedBinomial w), ∀ x : σ → ℤ,
      (xs.map (fun u => F.polynomialOrbitEval w x u.orbit)).prod = F.polynomialOrbitEval w x p := by
  obtain ⟨xs, hxs⟩ := F.exists_binomial_factorization w p
  refine ⟨xs, fun x => ?_⟩
  have h := congrArg (F.polynomialOrbitEval w x) hxs
  simpa only [map_list_prod, List.map_map, Function.comp_def] using h

theorem exists_integer_binomial_factorization (w : σ → ℕ) (p : F.PolynomialOrbit w) :
    ∃ xs : List (F.AdaptedBinomial w), ∀ x : σ → ℤ,
      (xs.map (fun u => (⟨(u.exponent.prod fun i n => ((Ring.choose (x i) n : ℤ) : ℚ)) •
        u.coefficient⟩ : F.Group))).prod = F.polynomialOrbitEval w x p := by
  simpa only [AdaptedBinomial.eval_eq_choose] using F.exists_binomial_factorization_eval w p

section Real

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]

theorem AdaptedBinomial.evalReal_coord {F : NilpotentLieFiltration L s} {w : σ → ℕ}
    (u : F.AdaptedBinomial w) (x : σ → ℝ) :
    (F.polynomialOrbitRealEval w x u.orbit).coord =
      MvPolynomial.aeval x (multivariateBinomial u.exponent) • u.coefficient := by
  rw [polynomialOrbitRealEval_coord, AdaptedBinomial.orbit_log, eval₂_tmul]

theorem AdaptedBinomial.evalReal_eq_choose {F : NilpotentLieFiltration L s} {w : σ → ℕ}
    (u : F.AdaptedBinomial w) (x : σ → ℝ) :
    F.polynomialOrbitRealEval w x u.orbit =
      (⟨(u.exponent.prod fun i n => Ring.choose (x i) n) • u.coefficient⟩ : F.Group) := by
  apply NilpotentLieBCHGroup.ext
  rw [u.evalReal_coord, multivariateBinomial_aeval_choose u.exponent x]

theorem exists_binomial_factorization_evalReal (w : σ → ℕ) (p : F.PolynomialOrbit w) :
    ∃ xs : List (F.AdaptedBinomial w), ∀ x : σ → ℝ,
      (xs.map (fun u => F.polynomialOrbitRealEval w x u.orbit)).prod =
        F.polynomialOrbitRealEval w x p := by
  obtain ⟨xs, hxs⟩ := F.exists_binomial_factorization w p
  refine ⟨xs, fun x => ?_⟩
  have h := congrArg (F.polynomialOrbitRealEval w x) hxs
  simpa only [map_list_prod, List.map_map, Function.comp_def] using h

theorem exists_real_binomial_factorization (w : σ → ℕ) (p : F.PolynomialOrbit w) :
    ∃ xs : List (F.AdaptedBinomial w), ∀ x : σ → ℝ,
      (xs.map (fun u => (⟨(u.exponent.prod fun i n => Ring.choose (x i) n) •
        u.coefficient⟩ : F.Group))).prod = F.polynomialOrbitRealEval w x p := by
  simpa only [AdaptedBinomial.evalReal_eq_choose] using F.exists_binomial_factorization_evalReal w p

end Real
end Erdos3.NilpotentLieFiltration

end

end OAI
