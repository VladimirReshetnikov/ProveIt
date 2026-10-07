/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.UnitProductOrbitFamily
import OAI.Combinatorics.Progressions.Nilpotent.RankInvariantNiltestBudget

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

structure NativeUnitRankFamily {σ : Type*} (w : σ → ℕ) (s r : ℕ)
    (τ I : Type*) [Fintype I] (p : ℝ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L s dim
  rank : model.DegreeRankStructure r
  complexity : rank.ComplexityLE p
  test : I → model.Niltest w
  test_norm : ∀ i, (test i).normBound = 1
  test_complexity : ∀ i, (test i).ComplexityLE p
  unit : ∀ x, ∑ i, ‖(test i).observable x‖ ^ 2 = 1
  orbit : τ → model.filtration.realification.PolynomialOrbit w
  normalized : ∀ t, model.filtration.realification.polynomialOrbitEval w 0 (orbit t) = 1

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra
  NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd
  NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff

namespace NativeUnitRankFamily

variable {σ τ I : Type*} [Fintype I] {w : σ → ℕ} {s r : ℕ} {p q : ℝ}
  (F : NativeUnitRankFamily w s r τ I p)

noncomputable def eval (t : τ) (i : I) (x : σ → ℤ) : ℂ :=
  (F.test i).observable (QuotientGroup.mk
    (F.model.filtration.realification.polynomialOrbitEval w x (F.orbit t)))

theorem unit_eval (t : τ) (x : σ → ℤ) : ∑ i, ‖F.eval t i x‖ ^ 2 = 1 :=
  F.unit _

theorem norm_eval (t : τ) (i : I) (x : σ → ℤ) : ‖F.eval t i x‖ ≤ 1 := by
  have h := (F.test i).norm_le (QuotientGroup.mk
    (F.model.filtration.realification.polynomialOrbitEval w x (F.orbit t)))
  rw [F.test_norm] at h
  exact h

noncomputable def mono (hpq : p ≤ q) : NativeUnitRankFamily w s r τ I q :=
  { F with
    complexity := F.complexity.mono F.rank hpq
    test_complexity := fun i => (F.test_complexity i).mono hpq }

@[simp] theorem mono_eval (hpq : p ≤ q) (t : τ) (i : I) (x : σ → ℤ) :
    (F.mono hpq).eval t i x = F.eval t i x := rfl

end NativeUnitRankFamily

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} (T : D.DegreeRankStructure r) {p : ℝ}
  (V : D.UnitVerticalObservable (T.realSubgroup s r) I p)

theorem rank_invariant_of_frequency_zero
    (hzero : ∀ x ∈ T.filtration.layer s r, V.frequency x = 0)
    (z : D.RealGroup) (hz : z ∈ T.realSubgroup s r) (i : I) (x : D.Space) :
    V.observable i (z • x) = V.observable i x := by
  have hle : T.filtration.layer s r ≤ V.frequency.ker := hzero
  have hr : realifyFunctional V.frequency z.coord = 0 :=
    (mem_realified_frequency_kernel_iff V.frequency z.coord).mp
      (Submodule.baseChange_mono ℝ hle hz)
  rw [V.vertical i z hz x, hr, AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

section Coordinates

variable {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {T : Subgroup D.RealGroup} {p : ℝ}
  (V : D.UnitVerticalObservable T I p)

noncomputable def coordinateNiltest {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i : I) : D.Niltest w where
  orbit := g
  observable := V.observable i
  normBound := 1
  lipBound := V.lipBound
  norm_le := V.norm i
  lipschitz := V.lipschitz i

theorem coordinateNiltest_complexity {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (i : I)
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) :
    (V.coordinateNiltest g i).ComplexityLE (p + 4) := by
  refine ⟨hD.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 : ℝ) + (V.lipBound : ℝ)) ≤ p + 4
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp p := by nlinarith [V.lip_bound, Real.one_le_exp hp]
    _ ≤ Real.exp 4 * Real.exp p := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (4 : ℝ)]) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, add_comm]

end Coordinates

theorem exists_lower_rank_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {r d : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure (r + 1))
      {p : ℝ} (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
      {w : σ → ℕ} (g : D.filtration.realification.PolynomialOrbit w),
      0 ≤ p → R.ComplexityLE p →
      (∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = 0) →
      ∃ n : ℕ, n ≤ d ∧
        ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
          ∃ U : Q.DegreeRankStructure r,
            ∃ hQF : Q.filtration = D.filtration.quotientLie
                (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal,
              U.filtration = R.filtration.quotientRank r (Nat.le_of_succ_le R.filtration.rank_le_degree) ∧
              Q.lattice = D.lattice.map (D.filtration.quotientStepHom
                (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal) ∧
              U.ComplexityLE ((p + C) ^ C) ∧
              (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
               letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
                 IsModuleTopology.topologicalAddGroup ℝ _
               letI := realification_moduleTopology_t2 Q.basis
               ∃ S : I → Q.Niltest w,
                 (∀ i, (S i).orbit = R.rankQuotientOrbit Q hQF g) ∧
                 (∀ i, (S i).normBound = 1) ∧
                 (∀ i, (S i).ComplexityLE ((p + C) ^ C)) ∧
                 (∀ y : Q.Space, ∑ i, ‖(S i).observable y‖ ^ 2 = 1) ∧
                 (∀ i x, (S i).observable (QuotientGroup.mk
                   (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                     (hM := Q.filtration.lowerCentralSeries_eq_bot)
                     (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x)) =
                   V.observable i (QuotientGroup.mk x)) ∧
                 ∀ i x, (S i).eval x = V.observable i
                   (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g))) := by
  obtain ⟨a, _, hdescent⟩ := DegreeRankStructure.exists_rankInvariant_niltest_budget s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 7) ^ 11
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((P + Polynomial.C a) ^ a + P)
  refine ⟨C, hC, ?_⟩
  intro L I σ _ _ _ _ _ _ _ r d D R p V w g hp hR hzero
  let q := (p + 7) ^ 11
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hp4q : p + 4 ≤ q := by
    apply (show p + 4 ≤ p + 7 by linarith).trans
    exact (pow_one (p + 7)).symm.le.trans
      (pow_le_pow_right₀ (by linarith) (by decide : 1 ≤ 11))
  have hbudget' : (q + a) ^ a + q ≤ (p + C) ^ C := by
    simpa [q, P, X, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (q + a) ^ a)).trans hbudget'
  have haC : (q + a) ^ a ≤ (p + C) ^ C := (le_add_of_nonneg_right hq).trans hbudget'
  obtain ⟨n, hn, Q, U, hU, hQF, hQL, hUc, he⟩ := R.exists_controlled_lower_rank_quotient hp hR
  have h11 : (p + 3) ^ 11 ≤ q := pow_le_pow_left₀ (by positivity) (by linarith) 11
  have h5 : (p + 3) ^ 5 ≤ q :=
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + 3) (by decide : 5 ≤ 11)).trans h11
  have hUq : U.ComplexityLE q := hUc.mono U h11
  refine ⟨n, hn, Q, U, hQF, hU, hQL, hUq.mono U hqC, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  have htests := fun i => hdescent R Q hQF hQL (V.coordinateNiltest g i) q hq
    ((V.coordinateNiltest_complexity g i hp hR.1).mono hp4q) hUq.1
    (fun i j => (he j i).trans h5)
    (fun z hz x => V.rank_invariant_of_frequency_zero R hzero z hz i x)
  choose S hSo hSn hSc hSp hSe using htests
  refine ⟨S, hSo, hSn, (fun i => (hSc i).mono haC), ?_, hSp, hSe⟩
  intro y
  induction y using Quotient.inductionOn with
  | h y =>
    obtain ⟨x, hx⟩ := D.filtration.realQuotientStepHom_surjective
      (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal y
    have heq : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x = y := hx
    rw [← heq]
    simpa only [hSp, coordinateNiltest] using V.unit (QuotientGroup.mk x)

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

def HasLowerRankUnitFamily {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure (r + 1))
    (v : I → D.Space → ℂ) {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (p : ℝ) : Prop :=
  ∃ n : ℕ, n ≤ d ∧
    ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
      ∃ U : Q.DegreeRankStructure r, U.ComplexityLE p ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
           IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 Q.basis
         ∃ a : Q.filtration.realification.PolynomialOrbit w,
           ∃ K : I → Q.Niltest w,
             (∀ i, (K i).orbit = a) ∧ (∀ i, (K i).normBound = 1) ∧
             (∀ i, (K i).ComplexityLE p) ∧
             (∀ y : Q.Space, ∑ i, ‖(K i).observable y‖ ^ 2 = 1) ∧
             ∀ i x, (K i).eval x = v i
               (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

universe u v t

theorem uniform_lower_rank_family {L : Type u} {I : Type v} {σ : Type t}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (R : D.DegreeRankStructure (r + 1)) {p : ℝ}
    (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
    (w : σ → ℕ) (hp : 0 ≤ p) (hR : R.ComplexityLE p)
    (hzero : ∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = 0) :
    let C := (exists_lower_rank_family.{u, v, t} s).choose
    ∃ n : ℕ, n ≤ d ∧
      ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
        ∃ U : Q.DegreeRankStructure r,
          ∃ hQF : Q.filtration = D.filtration.quotientLie
              (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal,
            U.filtration = R.filtration.quotientRank r
              (Nat.le_of_succ_le R.filtration.rank_le_degree) ∧
            Q.lattice = D.lattice.map (D.filtration.quotientStepHom
              (R.filtration.layerIdeal s (r + 1)) R.terminal_le_topRankIdeal) ∧
            U.ComplexityLE ((p + C) ^ C) ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
               IsModuleTopology.topologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 Q.basis
             ∃ S : I → Q.Niltest w,
               (∀ i, (S i).normBound = 1) ∧
               (∀ i, (S i).ComplexityLE ((p + C) ^ C)) ∧
               (∀ y : Q.Space, ∑ i, ‖(S i).observable y‖ ^ 2 = 1) ∧
               (∀ i x, (S i).observable (QuotientGroup.mk
                 (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                   (hM := Q.filtration.lowerCentralSeries_eq_bot)
                   (lieQuotientMap (R.filtration.layerIdeal s (r + 1))) x)) =
                 V.observable i (QuotientGroup.mk x)) ∧
               ∀ (g : D.filtration.realification.PolynomialOrbit w) i x,
                 ((S i).withOrbit (R.rankQuotientOrbit Q hQF g)).eval x =
                   V.observable i
                     (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g))) := by
  dsimp only
  obtain ⟨n, hn, Q, U, hQF, hUF, hQL, hUc, hS⟩ :=
    (exists_lower_rank_family.{u, v, t} s).choose_spec.2 D R V
      (1 : D.filtration.realification.PolynomialOrbit w) hp hR hzero
  refine ⟨n, hn, Q, U, hQF, hUF, hQL, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨S, _, hSn, hSc, hSu, hSp, _⟩ := hS
  refine ⟨S, hSn, hSc, hSu, hSp, ?_⟩
  intro g i x
  rw [Niltest.withOrbit_eval, R.rankQuotientOrbit_eval Q hQF]
  exact hSp i _

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

def HasUniformLowerRankUnitFamily {L I σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure (r + 1))
    (v : I → D.Space → ℂ) (w : σ → ℕ) (p : ℝ) : Prop :=
  ∃ n : ℕ, n ≤ d ∧
    ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
      ∃ U : Q.DegreeRankStructure r, U.ComplexityLE p ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
           IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 Q.basis
         ∃ K : I → Q.Niltest w,
           (∀ i, (K i).normBound = 1) ∧ (∀ i, (K i).ComplexityLE p) ∧
           (∀ y : Q.Space, ∑ i, ‖(K i).observable y‖ ^ 2 = 1) ∧
           ∃ a : D.filtration.realification.PolynomialOrbit w →
               Q.filtration.realification.PolynomialOrbit w,
             (∀ g, D.filtration.realification.polynomialOrbitEval w 0 g = 1 →
               Q.filtration.realification.polynomialOrbitEval w 0 (a g) = 1) ∧
             ∀ g i x, ((K i).withOrbit (a g)).eval x = v i
               (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g)))

theorem HasUniformLowerRankUnitFamily.atOrbit {L I σ : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
    {v : I → D.Space → ℂ} {w : σ → ℕ} {p : ℝ}
    (h : D.HasUniformLowerRankUnitFamily R v w p)
    (g : D.filtration.realification.PolynomialOrbit w) :
    D.HasLowerRankUnitFamily R v g p := by
  obtain ⟨n, hn, Q, U, hUc, hK⟩ := h
  refine ⟨n, hn, Q, U, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, _, hKe⟩ := hK
  exact ⟨a g, (fun i => (K i).withOrbit (a g)), (fun _ => rfl), hKn,
    (fun i => ((K i).withOrbit_complexity (a g) p).mpr (hKc i)), hKu, hKe g⟩

universe u v t

theorem UnitVerticalObservable.hasUniformLowerRankUnitFamily
    {L : Type u} {I : Type v} {σ : Type t}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (R : D.DegreeRankStructure (r + 1)) {p : ℝ}
    (V : D.UnitVerticalObservable (R.realSubgroup s (r + 1)) I p)
    (w : σ → ℕ) (hp : 0 ≤ p) (hR : R.ComplexityLE p)
    (hzero : ∀ x ∈ R.filtration.layer s (r + 1), V.frequency x = 0) :
    let C := (UnitVerticalObservable.exists_lower_rank_family.{u, v, t} s).choose
    D.HasUniformLowerRankUnitFamily R V.observable w ((p + C) ^ C) := by
  obtain ⟨n, hn, Q, U, hQF, _, _, hUc, hK⟩ :=
    UnitVerticalObservable.uniform_lower_rank_family D R V w hp hR hzero
  refine ⟨n, hn, Q, U, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, _, hKe⟩ := hK
  refine ⟨K, hKn, hKc, hKu, R.rankQuotientOrbit Q hQF, ?_, hKe⟩
  intro g hg
  rw [R.rankQuotientOrbit_eval Q hQF, hg]
  exact map_one _

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

def HasLowerRankOrbitFamily {L I σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
    {s r d : ℕ} (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure (r + 1))
    (w : σ → ℕ) (f : τ → I → (σ → ℤ) → ℂ) (p : ℝ) : Prop :=
  ∃ n : ℕ, n ≤ d ∧
    ∃ Q : RationalFilteredNilmanifold (L ⧸ R.filtration.layerIdeal s (r + 1)) s n,
      ∃ U : Q.DegreeRankStructure r, U.ComplexityLE p ∧
        (letI := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
         letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
           IsModuleTopology.topologicalAddGroup ℝ _
         letI := realification_moduleTopology_t2 Q.basis
         ∃ K : I → Q.Niltest w,
           (∀ i, (K i).normBound = 1) ∧ (∀ i, (K i).ComplexityLE p) ∧
           (∀ y : Q.Space, ∑ i, ‖(K i).observable y‖ ^ 2 = 1) ∧
           ∃ a : τ → Q.filtration.realification.PolynomialOrbit w,
             (∀ t, Q.filtration.realification.polynomialOrbitEval w 0 (a t) = 1) ∧
             ∀ t i x, ((K i).withOrbit (a t)).eval x = f t i x)

theorem HasUniformLowerRankUnitFamily.realizeFamily {L I σ τ : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
    {v : I → D.Space → ℂ} {w : σ → ℕ} {p : ℝ}
    (h : D.HasUniformLowerRankUnitFamily R v w p)
    (f : τ → I → (σ → ℤ) → ℂ)
    (hf : ∀ t, ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.filtration.realification.polynomialOrbitEval w 0 g = 1 ∧
      ∀ i x, v i (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval w x g)) = f t i x) :
    D.HasLowerRankOrbitFamily R w f p := by
  classical
  choose b hb0 hb using hf
  obtain ⟨n, hn, Q, U, hUc, hK⟩ := h
  refine ⟨n, hn, Q, U, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, ha0, hKe⟩ := hK
  exact ⟨K, hKn, hKc, hKu, (fun t => a (b t)),
    (fun t => ha0 (b t) (hb0 t)),
    fun t i x => (hKe (b t) i x).trans (hb t i x)⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

theorem HasLowerRankOrbitFamily.mono {L I σ τ : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
    {w : σ → ℕ} {f : τ → I → (σ → ℤ) → ℂ} {p q : ℝ}
    (h : D.HasLowerRankOrbitFamily R w f p) (hpq : p ≤ q) :
    D.HasLowerRankOrbitFamily R w f q := by
  obtain ⟨n, hn, Q, U, hUc, hK⟩ := h
  refine ⟨n, hn, Q, U, hUc.mono U hpq, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, ha0, hKe⟩ := hK
  exact ⟨K, hKn, (fun i => (hKc i).mono hpq), hKu, a, ha0, hKe⟩

theorem exists_lower_rank_product_family {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {I : ι → Type*} [∀ i, Fintype (I i)]
    {s r : ℕ} {d : ι → ℕ}
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (R : ∀ i, (D i).DegreeRankStructure (r + 1))
    (w : σ → ℕ) (f : ∀ i, τ → I i → (σ → ℤ) → ℂ) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (h : ∀ i, (D i).HasLowerRankOrbitFamily (R i) w (f i) p) :
    ∃ n : ι → ℕ, (∀ i, n i ≤ d i) ∧
      ∃ Q : ∀ i, RationalFilteredNilmanifold (L i ⧸ (R i).filtration.layerIdeal s (r + 1)) s (n i),
        ∃ U : ∀ i, (Q i).DegreeRankStructure r,
          (piRank Q U).ComplexityLE (productNiltestBudget p) ∧
          (letI : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
             fun _ => moduleTopology ℝ _
           letI : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
             fun _ => IsModuleTopology.topologicalAddGroup ℝ _
           letI : ∀ i, T2Space (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
             fun i => realification_moduleTopology_t2 (Q i).basis
           letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i ⧸ (R i).filtration.layerIdeal s (r + 1)))
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 (pi Q).basis
           ∃ K : (∀ i, I i) → (pi Q).Niltest w,
             (∀ j, (K j).normBound = 1) ∧
             (∀ j, (K j).ComplexityLE (productNiltestBudget p)) ∧
             (∀ x, ∑ j, ‖(K j).observable x‖ ^ 2 = 1) ∧
             ∃ a : τ → (pi Q).filtration.realification.PolynomialOrbit w,
               (∀ t, (pi Q).filtration.realification.polynomialOrbitEval w 0 (a t) = 1) ∧
               ∀ t j x, ((K j).withOrbit (a t)).eval x = ∏ i, f i t (j i) x) := by
  classical
  choose n hn Q U hUc hK using h
  refine ⟨n, hn, Q, U,
    (piRank_complexity Q U hp hι hUc).mono _ (productNiltestBudget_geometry hp), ?_⟩
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
    fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
    fun i => realification_moduleTopology_t2 (Q i).basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i ⧸ (R i).filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi Q).basis
  choose K hKn hKc hKu a ha0 hKe using hK
  obtain ⟨_, V, hVn, hVc, hVu, hVa, hVe⟩ := exists_normalized_product_unit_family Q K U hp hι hUc
    (fun i j => (hKn i j).le) hKc hKu (fun t i => a i t) (fun t i => ha0 i t)
  refine ⟨V, hVn, hVc, hVu,
    (fun t => NilpotentLieFiltration.piRealOrbit (fun i => (Q i).filtration) (fun i => a i t)),
    hVa, ?_⟩
  intro t j x
  rw [hVe]
  exact Finset.prod_congr rfl (fun i _ => hKe i t (j i) x)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

theorem exists_binary_lower_rank_unit_family
    {σ τ : Type*} {I J L₀ L₁ : Type} [Fintype I] [Fintype J]
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing L₁] [LieAlgebra ℚ L₁]
    {s r d₀ d₁ : ℕ} (D₀ : RationalFilteredNilmanifold L₀ s d₀)
    (D₁ : RationalFilteredNilmanifold L₁ s d₁)
    (R₀ : D₀.DegreeRankStructure (r + 1)) (R₁ : D₁.DegreeRankStructure (r + 1))
    (w : σ → ℕ) (f₀ : τ → I → (σ → ℤ) → ℂ) (f₁ : τ → J → (σ → ℤ) → ℂ)
    {p : ℝ} (hp : 2 ≤ p)
    (h₀ : D₀.HasLowerRankOrbitFamily R₀ w f₀ p)
    (h₁ : D₁.HasLowerRankOrbitFamily R₁ w f₁ p) :
    ∃ F : NativeUnitRankFamily w s r τ (I × J) (productNiltestBudget p),
      F.dim ≤ d₀ + d₁ ∧ ∀ t ij x, F.eval t ij x = f₀ t ij.1 x * f₁ t ij.2 x := by
  classical
  let D := optionFactors D₀ (fun _ : Unit => D₁)
  let R : ∀ i : Option Unit, (D i).DegreeRankStructure (r + 1)
    | none => R₀
    | some _ => R₁
  let K : Option Unit → Type
    | none => I
    | some _ => J
  let : ∀ i, Fintype (K i) := fun i => match i with
    | none => inferInstanceAs (Fintype I)
    | some _ => inferInstanceAs (Fintype J)
  let f : ∀ i, τ → K i → (σ → ℤ) → ℂ
    | none => f₀
    | some _ => f₁
  have h : ∀ i, (D i).HasLowerRankOrbitFamily (R i) w (f i) p := fun i => by
    match i with
    | none => exact h₀
    | some _ => exact h₁
  obtain ⟨n, hn, Q, U, hU, hfamily⟩ := exists_lower_rank_product_family D R w f
    (by linarith) (by simpa using hp) h
  let L (i : Option Unit) :=
    optionLieSpace L₀ (fun _ : Unit => L₁) i ⧸ (R i).filtration.layerIdeal s (r + 1)
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i) := fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] L i) := fun i => realification_moduleTopology_t2 (Q i).basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi Q).basis
  obtain ⟨V, hVn, hVc, hVu, a, ha, he⟩ := hfamily
  let e : (∀ i, K i) ≃ I × J := {
    toFun := fun k => (k none, k (some ()))
    invFun := fun ij i => match i with
      | none => ij.1
      | some _ => ij.2
    left_inv := by
      intro k
      funext i
      rcases i with _ | ⟨⟩ <;> rfl
    right_inv := fun _ => rfl
  }
  let F : NativeUnitRankFamily w s r τ (I × J) (productNiltestBudget p) := {
    L := ∀ i, L i
    dim := Fintype.card (Σ i : Option Unit, Fin (n i))
    model := pi Q
    rank := piRank Q U
    complexity := hU
    test := fun ij => V (e.symm ij)
    test_norm := fun ij => hVn (e.symm ij)
    test_complexity := fun ij => hVc (e.symm ij)
    unit := fun x => (e.symm.sum_comp (fun k => ‖(V k).observable x‖ ^ 2)).trans (hVu x)
    orbit := a
    normalized := ha
  }
  refine ⟨F, ?_, ?_⟩
  · change Fintype.card (Σ i : Option Unit, Fin (n i)) ≤ d₀ + d₁
    simp only [Fintype.card_sigma, Fintype.card_fin]
    rw [Fintype.sum_option, Fintype.sum_unique]
    exact Nat.add_le_add (hn none) (hn (some ()))
  · intro t ij x
    have hprod := he t (e.symm ij) x
    rw [Fintype.prod_option, Fintype.prod_unique] at hprod
    exact hprod

end Erdos3.RationalFilteredNilmanifold

end

end OAI
