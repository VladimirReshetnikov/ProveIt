/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.NativeEquivalenceTransitivity

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realificationLieHom_id_apply {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (x : ℝ ⊗[ℚ] L) : realificationLieHom (LieHom.id : L →ₗ⁅ℚ⁆ L) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

namespace RationalFilteredNilmanifold

open Module
open scoped NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (hst : s ≤ t)

noncomputable def raiseStepProjection : (D.raiseStep hst).Space → D.Space :=
  cosetMap (D.raiseStep hst).realLattice D.realLattice
    (NilpotentLieBCHGroup.realificationMap
      (hnil := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L))
    (NilpotentLieBCHGroup.realificationMap_subgroup (LieHom.id : L →ₗ⁅ℚ⁆ L)
      (D.raiseStep hst).lattice D.lattice (D.raiseStep_lattice_back hst))

theorem raiseStepProjection_mk (x : (D.raiseStep hst).RealGroup) :
    D.raiseStepProjection hst (QuotientGroup.mk x) =
      QuotientGroup.mk (NilpotentLieBCHGroup.realificationMap
        (hnil := (D.raiseStep hst).filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (LieHom.id : L →ₗ⁅ℚ⁆ L) x) := rfl

section Metric

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem raiseStepProjection_lipschitz :
    let := (D.raiseStep hst).metricSpace
    let := D.metricSpace
    LipschitzWith (coordinateLipschitzBound d d 1) (D.raiseStepProjection hst) := by
  let := realificationQuotientMetricSpace (D.raiseStep hst).basis (D.raiseStep hst).lattice
    (D.raiseStep hst).grid (D.raiseStep hst).grid_pos (D.raiseStep hst).outer_grid
  let := realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid
  have hentry (k i : Fin d) :
      RationalHeightLE (D.basis.repr ((LieHom.id : L →ₗ⁅ℚ⁆ L) ((D.raiseStep hst).basis i)) k) 1 := by
    change RationalHeightLE (D.basis.repr (D.basis i) k) 1
    rw [Basis.repr_self]
    by_cases h : i = k <;> simp [h, RationalHeightLE]
  have h := NilpotentLieBCHGroup.lipschitz_realificationMap_quotient
    (D.raiseStep hst).basis D.basis (LieHom.id : L →ₗ⁅ℚ⁆ L)
    (D.raiseStep hst).lattice D.lattice (D.raiseStep_lattice_back hst)
    (D.raiseStep hst).grid D.grid (D.raiseStep hst).grid_pos D.grid_pos
    (D.raiseStep hst).outer_grid D.outer_grid 1 hentry
  exact h.weaken (by simp only [Fintype.card_fin, Nat.cast_one, le_refl])

end Metric

noncomputable def raiseStepRealOrbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) :
    (D.raiseStep hst).filtration.realification.PolynomialOrbit w :=
  NilpotentLieFiltration.polynomialOrbitOfLog g.log g.adapted

theorem raiseStepRealOrbit_log {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) :
    (D.raiseStepRealOrbit hst g).log = g.log := rfl

theorem raiseStepProjection_orbit {σ : Type*} {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (x : σ → ℤ) :
    D.raiseStepProjection hst (QuotientGroup.mk
      ((D.raiseStep hst).filtration.realification.polynomialOrbitEval w x
        (D.raiseStepRealOrbit hst g))) =
      QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w x g) := by
  rw [D.raiseStepProjection_mk]
  apply congrArg (QuotientGroup.mk : D.RealGroup → D.Space)
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (LieHom.id : L →ₗ⁅ℚ⁆ L)
    (VectorPolynomial.eval (fun i => (x i : ℚ)) g.log) =
      VectorPolynomial.eval (fun i => (x i : ℚ)) g.log
  exact realificationLieHom_id_apply _

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

def raisedNiltestBudget (p : ℝ) : ℝ := p + (p + 2) ^ 2 + 3

theorem le_raisedNiltestBudget (p : ℝ) : p ≤ raisedNiltestBudget p := by
  unfold raisedNiltestBudget
  nlinarith [sq_nonneg (p + 2)]

namespace RationalFilteredNilmanifold.Niltest

open scoped TensorProduct NNReal

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def raiseStep (T : D.Niltest w) (hst : s ≤ t) : (D.raiseStep hst).Niltest w where
  orbit := D.raiseStepRealOrbit hst T.orbit
  observable := fun z => T.observable (D.raiseStepProjection hst z)
  normBound := T.normBound
  lipBound := T.lipBound * coordinateLipschitzBound d d 1
  norm_le z := T.norm_le _
  lipschitz := by
    let := (D.raiseStep hst).metricSpace
    let := D.metricSpace
    exact T.lipschitz.comp (D.raiseStepProjection_lipschitz hst)

theorem raiseStep_eval (T : D.Niltest w) (hst : s ≤ t) (x : σ → ℤ) :
    (T.raiseStep hst).eval x = T.eval x := by
  change T.observable (D.raiseStepProjection hst (QuotientGroup.mk
    ((D.raiseStep hst).filtration.realification.polynomialOrbitEval w x
      (D.raiseStepRealOrbit hst T.orbit)))) = T.eval x
  rw [D.raiseStepProjection_orbit]
  rfl

theorem raiseStep_evalCyclic (T : D.Niltest w) (hst : s ≤ t)
    (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    (T.raiseStep hst).evalCyclic N x = T.evalCyclic N x :=
  T.raiseStep_eval hst _

theorem raiseStep_unit_interval (T : D.Niltest w) (hst : s ≤ t) (hT : T.UnitIntervalValued) :
    (T.raiseStep hst).UnitIntervalValued := fun z => hT (D.raiseStepProjection hst z)

theorem raiseStep_complexity (T : D.Niltest w) (hst : s ≤ t) {p : ℝ}
    (hp : 0 ≤ p) (hT : T.ComplexityLE p) :
    (T.raiseStep hst).ComplexityLE (raisedNiltestBudget p) := by
  refine ⟨GeometryComplexityLE.mono (D.raiseStep hst)
    (D.raiseStep_geometry hst hT.1) (le_raisedNiltestBudget p), ?_⟩
  have hraw := T.observable_budget hT
  have hn : (T.normBound : ℝ) ≤ Real.exp p := by linarith [T.lipBound.coe_nonneg]
  have hl : (T.lipBound : ℝ) ≤ Real.exp p := by linarith [T.normBound.coe_nonneg]
  have hK := coordinateLipschitzBound_le_exp d d 1 hp hT.1.1 hT.1.1
    (by simpa using Real.one_le_exp_iff.mpr hp)
  have hn' : (T.normBound : ℝ) ≤ Real.exp (p + (p + 2) ^ 2) :=
    hn.trans (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (p + 2)]))
  have hl' : (T.lipBound : ℝ) * (coordinateLipschitzBound d d 1 : ℝ) ≤
      Real.exp (p + (p + 2) ^ 2) := by
    rw [Real.exp_add]
    exact mul_le_mul hl hK (by positivity) (Real.exp_nonneg _)
  have hone : 1 ≤ Real.exp (p + (p + 2) ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hsum : 2 + (T.normBound : ℝ) +
      (T.lipBound : ℝ) * (coordinateLipschitzBound d d 1 : ℝ) ≤
        Real.exp (raisedNiltestBudget p) := by
    calc
      _ ≤ 4 * Real.exp (p + (p + 2) ^ 2) := by linarith
      _ ≤ Real.exp 3 * Real.exp (p + (p + 2) ^ 2) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; unfold raisedNiltestBudget; ring
  change Real.log (2 + (T.normBound : ℝ) +
    (T.lipBound : ℝ) * (coordinateLipschitzBound d d 1 : ℝ)) ≤ raisedNiltestBudget p
  exact (Real.log_le_iff_le_exp (by positivity)).mpr hsum

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem raiseStep_top_vertical (T : D.Niltest w) (hst : s < t)
    (z : (D.raiseStep hst.le).RealGroup)
    (hz : z ∈ (D.raiseStep hst.le).filtration.realification.subgroup t)
    (x : (D.raiseStep hst.le).Space) :
    (T.raiseStep hst.le).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) *
          (T.raiseStep hst.le).observable x := by
  have hz' : z = 1 := by
    apply NilpotentLieBCHGroup.ext
    change z.coord = 0
    change z.coord ∈ D.filtration.realification.layer t at hz
    simpa only [D.filtration.realification.layer_eq_bot_above_step hst,
      Submodule.mem_bot] using hz
  subst z
  simp

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t n : ℕ}

theorem raiseStep_top_subgroup_eq_bot (D : RationalFilteredNilmanifold L s n)
    (hst : s < t) :
    (D.raiseStep hst.le).filtration.realification.subgroup t = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  change z = 1
  apply NilpotentLieBCHGroup.ext
  change z.coord = 0
  change z.coord ∈ D.filtration.realification.layer t at hz
  simpa only [D.filtration.realification.layer_eq_bot_above_step hst,
    Submodule.mem_bot] using hz

theorem raiseStep_observable_top_vertical (D : RationalFilteredNilmanifold L s n)
    (hst : s < t) (f : (D.raiseStep hst.le).Space → ℂ)
    (z : (D.raiseStep hst.le).RealGroup)
    (hz : z ∈ (D.raiseStep hst.le).filtration.realification.subgroup t)
    (x : (D.raiseStep hst.le).Space) :
    f (z • x) =
      CircleFourier.character
        ((realifyFunctional (0 : L →ₗ[ℚ] ℚ) z.coord : ℝ) : CircleFourier.Circle) * f x := by
  have hz' : z = 1 := by
    simpa only [raiseStep_top_subgroup_eq_bot D hst, Subgroup.mem_bot] using hz
  subst z
  simp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

universe u

theorem cyclic_upperComparison_mul_niltest
    {degree low N : ℕ} [NeZero N] {P R error : ℝ}
    (f g : ZMod N → ℝ) (hcompare : CyclicNiltestUpperComparison.{u} degree N P error f g)
    (hlow : low ≤ degree) (hR : 0 ≤ R)
    (hBudget : productNiltestBudget (raisedNiltestBudget R) ≤ P)
    {L₁ : Type u} [lie₁ : LieRing L₁] [alg₁ : LieAlgebra ℚ L₁] {s₁ dim₁ : ℕ}
    [top₁ : TopologicalSpace (ℝ ⊗[ℚ] L₁)] [add₁ : IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
    [smul₁ : ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [t2₁ : T2Space (ℝ ⊗[ℚ] L₁)]
    (D₁ : RationalFilteredNilmanifold L₁ s₁ dim₁) (hs₁ : s₁ ≤ degree)
    (A : D₁.Niltest (fun _ : Unit => 1)) (hA : A.UnitIntervalValued) (hAc : A.ComplexityLE R) :
    CyclicNiltestUpperComparison.{u} low N R error
      (fun x => f x * (A.evalCyclic N (fun _ => x)).re)
      (fun x => g x * (A.evalCyclic N (fun _ => x)).re) := by
  intro L₂ lie₂ alg₂ s₂ dim₂ top₂ add₂ smul₂ t2₂ D₂ hs₂ T hT hTc
  let K : Bool → Type u := BoolLieFamily L₁ L₂
  let dims : Bool → ℕ := fun b => Bool.rec dim₂ dim₁ b
  let D : ∀ b, RationalFilteredNilmanifold (K b) degree (dims b) := fun b => by
    cases b
    · exact D₂.raiseStep (hs₂.trans hlow)
    · exact D₁.raiseStep hs₁
  let U : ∀ b, (D b).Niltest (fun _ : Unit => 1) := fun b => by
    cases b
    · exact T.raiseStep (hs₂.trans hlow)
    · exact A.raiseStep hs₁
  have hUc : ∀ b, (U b).ComplexityLE (raisedNiltestBudget R) := by
    intro b
    cases b
    · exact T.raiseStep_complexity (hs₂.trans hlow) hR hTc
    · exact A.raiseStep_complexity hs₁ hR hAc
  have hU : ∀ b, (U b).UnitIntervalValued := by
    intro b
    cases b
    · exact T.raiseStep_unit_interval (hs₂.trans hlow) hT
    · exact A.raiseStep_unit_interval hs₁ hA
  have hR' : 0 ≤ raisedNiltestBudget R := hR.trans (le_raisedNiltestBudget R)
  have hcard : (Fintype.card Bool : ℝ) ≤ raisedNiltestBudget R := by
    norm_num only [Fintype.card_bool, Nat.cast_ofNat]
    unfold raisedNiltestBudget
    nlinarith [sq_nonneg (R + 2)]
  let : FiniteDimensional ℚ (∀ b, K b) :=
    (RationalFilteredNilmanifold.productFinBasis D).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ b, K b))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ b, K b)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ b, K b)) :=
    realification_moduleTopology_t2 (RationalFilteredNilmanifold.productFinBasis D)
  let S := RationalFilteredNilmanifold.piNiltest D U hR' hcard hUc
  have hSc : S.ComplexityLE P :=
    (RationalFilteredNilmanifold.piNiltest_complexity D U hR' hcard hUc).mono hBudget
  have hSu : S.UnitIntervalValued :=
    RationalFilteredNilmanifold.piNiltest_unit_interval D U hR' hcard hUc hU
  have h := hcompare (RationalFilteredNilmanifold.pi D) le_rfl S hSu hSc
  have heval (x : ZMod N) : S.evalCyclic N (fun _ : Unit => x) =
      A.evalCyclic N (fun _ : Unit => x) * T.evalCyclic N (fun _ : Unit => x) := by
    change (RationalFilteredNilmanifold.piNiltest D U hR' hcard hUc).eval
      (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.piNiltest_eval, Fintype.prod_bool]
    change (A.raiseStep hs₁).eval (fun _ : Unit => (x.val : ℤ)) *
      (T.raiseStep (hs₂.trans hlow)).eval (fun _ : Unit => (x.val : ℤ)) = _
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_eval,
      RationalFilteredNilmanifold.Niltest.raiseStep_eval]
    rfl
  convert h using 1
  apply Finset.expect_congr rfl
  intro x _
  rw [heval, Complex.mul_re, (A.unit_interval_evalCyclic hA N (fun _ => x)).1,
    (T.unit_interval_evalCyclic hT N (fun _ => x)).1]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

inductive PositiveCyclicNiltest.{u} (degree N : ℕ) [NeZero N] (p : ℝ)
    (f : ZMod N → ℝ) : Prop where
  | of_test {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s dim) (hdegree : s ≤ degree)
      (T : D.Niltest (fun _ : Unit => 1)) (hpositive : T.UnitIntervalValued)
      (hcomplexity : T.ComplexityLE p)
      (heval : ∀ x, f x = (T.evalCyclic N (fun _ => x)).re) :
      PositiveCyclicNiltest degree N p f

namespace PositiveCyclicNiltest

universe u

theorem unit_interval {degree N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℝ}
    (hf : PositiveCyclicNiltest.{u} degree N p f) (x : ZMod N) :
    0 ≤ f x ∧ f x ≤ 1 := by
  rcases hf with ⟨D, hs, T, hT, hTc, heval⟩
  rw [heval]
  exact (T.unit_interval_evalCyclic hT N (fun _ => x)).2

theorem mono {degree degree' N : ℕ} [NeZero N] {p p' : ℝ} {f : ZMod N → ℝ}
    (hf : PositiveCyclicNiltest.{u} degree N p f) (hdegree : degree ≤ degree')
    (hp : p ≤ p') : PositiveCyclicNiltest.{u} degree' N p' f := by
  rcases hf with ⟨D, hs, T, hT, hTc, heval⟩
  exact .of_test D (hs.trans hdegree) T hT (hTc.mono hp) heval

theorem mul_upperComparison {degree low N : ℕ} [NeZero N] {P R error : ℝ}
    {a f g : ZMod N → ℝ} (ha : PositiveCyclicNiltest.{u} degree N R a)
    (hcompare : CyclicNiltestUpperComparison.{u} degree N P error f g)
    (hlow : low ≤ degree) (hR : 0 ≤ R)
    (hBudget : productNiltestBudget (raisedNiltestBudget R) ≤ P) :
    CyclicNiltestUpperComparison.{u} low N R error
      (fun x => f x * a x) (fun x => g x * a x) := by
  rcases ha with @⟨L, lie, alg, s, dim, top, add, smul, t2, D, hs, T, hT, hTc, heval⟩
  have heq : a = fun x => (T.evalCyclic N (fun _ => x)).re := funext heval
  rw [heq]
  exact @cyclic_upperComparison_mul_niltest degree low N _ P R error
    f g @hcompare hlow hR hBudget L lie alg s dim top add smul t2 D hs T hT hTc

theorem apply_shiftBound {degree N : ℕ} [NeZero N] {p error : ℝ}
    {a J c : ZMod N → ℝ} {E : Finset (ZMod N)}
    (hc : PositiveCyclicNiltest.{u} degree N p c)
    (hbound : CyclicNiltestShiftBound.{u} degree N p error a J E)
    {h : ZMod N} (hh : h ∉ E) :
    (𝔼 n, a n * J (n + h) * c n) ≤ error := by
  rcases hc with ⟨D, hs, T, hT, hTc, heval⟩
  simp_rw [heval]
  exact hbound h hh D hs T hT hTc

end PositiveCyclicNiltest
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

universe u

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def complement (T : D.Niltest w) : D.Niltest w where
  orbit := T.orbit
  observable := fun z => 1 - T.observable z
  normBound := 1 + T.normBound
  lipBound := T.lipBound
  norm_le z := by
    exact (norm_sub_le _ _).trans (by simpa using add_le_add_left (T.norm_le z) 1)
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he : (1 - T.observable x) - (1 - T.observable y) =
        -(T.observable x - T.observable y) := by ring
    rw [dist_eq_norm, he, norm_neg]
    simpa only [dist_eq_norm] using T.lipschitz.dist_le_mul x y

theorem complement_evalCyclic (T : D.Niltest w) (N : ℕ) [NeZero N] (x : σ → ZMod N) :
    T.complement.evalCyclic N x = 1 - T.evalCyclic N x := rfl

theorem complement_unitInterval (T : D.Niltest w) (hT : T.UnitIntervalValued) :
    T.complement.UnitIntervalValued := by
  intro z
  have hz := hT z
  change (1 - T.observable z).im = 0 ∧ 0 ≤ (1 - T.observable z).re ∧
    (1 - T.observable z).re ≤ 1
  simp only [Complex.sub_im, Complex.one_im, Complex.sub_re, Complex.one_re, hz.1]
  exact ⟨by norm_num, by linarith [hz.2.2], by linarith [hz.2.1]⟩

theorem complement_complexity (T : D.Niltest w) {p : ℝ}
    (hT : T.ComplexityLE p) : T.complement.ComplexityLE (p + 1) := by
  refine ⟨hT.1.mono D (by linarith), ?_⟩
  change Real.log (2 + (1 + (T.normBound : ℝ)) + (T.lipBound : ℝ)) ≤ p + 1
  apply (Real.log_le_iff_le_exp (by positivity)).2
  rw [Real.exp_add]
  have hcap := T.observable_budget hT
  nlinarith [Real.add_one_le_exp (1 : ℝ), T.normBound.coe_nonneg, T.lipBound.coe_nonneg]

end RationalFilteredNilmanifold.Niltest

theorem PositiveCyclicNiltest.complement {degree N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℝ} (hf : PositiveCyclicNiltest.{u} degree N p f) :
    PositiveCyclicNiltest.{u} degree N (p + 1) (fun x => 1 - f x) := by
  rcases hf with ⟨D, hs, T, hT, hTc, heval⟩
  refine .of_test D hs T.complement (T.complement_unitInterval hT)
    (T.complement_complexity hTc) ?_
  intro x
  rw [T.complement_evalCyclic, Complex.sub_re, Complex.one_re, heval]

theorem CyclicNiltestUpperComparison.test_positive {degree N : ℕ} [NeZero N]
    {P R error : ℝ} {f g a : ZMod N → ℝ}
    (hcompare : CyclicNiltestUpperComparison.{u} degree N P error f g)
    (ha : PositiveCyclicNiltest.{u} degree N R a) (hRP : R ≤ P) :
    (𝔼 x, (f x - g x) * a x) ≤ error := by
  rcases ha with ⟨D, hs, T, hT, hTc, heval⟩
  simpa only [heval] using hcompare D hs T hT (hTc.mono hRP)

end Erdos3

end

end OAI
