import OAI.Combinatorics.Progressions.Dynamics.FrozenCorrelationBudget
import OAI.Combinatorics.Progressions.Estimates.NativeFixedFactoredQuadruples
import OAI.Combinatorics.Progressions.Estimates.NativePartitionFreezing
import OAI.Combinatorics.Progressions.Estimates.NativePositiveCorrelation
import OAI.Combinatorics.Progressions.Lattices.NativeIntervalResiduePartition

namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def replacedRankResidual (h : ZMod N)
    (c : Fin W.family.outputDim → ZMod N → ℂ)
    (ij : Fin W.mixed.outputDim × Fin W.family.outputDim) (x : ZMod N) : ℂ :=
  multiplicativeDerivative f h x * star (W.mixed.evalCyclic N ij.1 (correlationInput h x)) *
    star (c ij.2 x)

theorem exists_rank_approximation_correlation {J : Type*} [Fintype J]
    (hf : ∀ x, ‖f x‖ ≤ 1) (h : W.shifts) (A : J → ZMod N → ℝ)
    (c : J → Fin W.family.outputDim → ZMod N → ℂ) {q : ℝ}
    (hq : 2 ≤ q) (hcard : (Fintype.card J : ℝ) ≤ Real.exp q)
    (hA : ∀ j, PositiveCyclicNiltest.{0} (s - 1) N q (A j))
    (herr : (𝔼 x, ‖W.selectedRank h x -
      ∑ j, (A j x : ℂ) * c j (W.selectedWitness h).coordinate.2 x‖) ≤ Real.exp (-(2 * p)) / 2) :
    ∃ j, Nonempty (NativeVectorCorrelation (s - 1) N
      (productNiltestBudget (raisedNiltestBudget (p + q + 2))) (W.replacedRankResidual h.val (c j))) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let b (x : ZMod N) := W.selectedMixed h x * W.selectedLower h x
  have hb (x : ZMod N) : ‖b x‖ ≤ Real.exp p := by
    have hm := W.mixed.norm_eval (W.selectedWitness h).coordinate.1
      (fun i => (((correlationInput h.val x) i).val : ℤ))
    have hl := (W.selectedWitness h).test.eval_budget (W.selectedWitness h).complexity
      (fun _ : Unit => (x.val : ℤ))
    exact (norm_mul _ _).trans_le ((mul_le_mul hm hl (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  let v (j : J) (x : ZMod N) := (A j x : ℂ) * c j (W.selectedWitness h).coordinate.2 x * b x
  have hmean : (𝔼 x, ‖W.selectedProduct h x - ∑ j, v j x‖) ≤ Real.exp (-p) / 2 := by
    have he := mean_error_mul_bounded (W.selectedRank h)
      (fun x => ∑ j, (A j x : ℂ) * c j (W.selectedWitness h).coordinate.2 x) b
      (Real.exp_pos p).le hb herr
    have hid (x : ZMod N) : W.selectedProduct h x - ∑ j, v j x =
        W.selectedRank h x * b x -
        (∑ j, (A j x : ℂ) * c j (W.selectedWitness h).coordinate.2 x) * b x := by
      rw [Finset.sum_mul]
      simp only [v, b, W.selectedProduct_eq]
      ring
    have hexp : Real.exp p * (Real.exp (-(2 * p)) / 2) = Real.exp (-p) / 2 := by
      rw [← mul_div_assoc, ← Real.exp_add]
      congr 2
      ring
    simpa only [hid, hexp] using he
  obtain ⟨j, hj⟩ := exists_correlating_summand_of_mean (multiplicativeDerivative f h.val)
    (W.selectedProduct h) v (Real.exp_pos (-p)) (Real.exp_pos q) hcard
    (multiplicativeDerivative_norm_le_one f hf h.val) hmean (W.selectedProduct_correlation h)
  have hthreshold : Real.exp (-(p + q + 2)) ≤ Real.exp (-p) / (2 * Real.exp q) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have he : Real.exp (-(p + q + 2)) * (2 * Real.exp q) = 2 * Real.exp (-p - 2) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    rw [he]
    have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    calc
      _ ≤ Real.exp 2 * Real.exp (-p - 2) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
      _ = Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
  have hpR : p ≤ p + q + 2 := by linarith
  have hqR : q ≤ p + q + 2 := by linarith
  let V : NativeVectorCorrelation (s - 1) N (p + q + 2)
      (fun ij x => (A j x : ℂ) * W.replacedRankResidual h.val (c j) ij x) := {
    L := (W.selectedWitness h).L
    dim := (W.selectedWitness h).dim
    model := (W.selectedWitness h).model
    test := (W.selectedWitness h).test
    complexity := (W.selectedWitness h).complexity.mono hpR
    coordinate := (W.selectedWitness h).coordinate
    correlation := by
      have hc := hthreshold.trans hj
      have heq (x : ZMod N) : multiplicativeDerivative f h.val x * star (v j x) =
          ((A j x : ℂ) * W.replacedRankResidual h.val (c j) (W.selectedWitness h).coordinate x) *
            star ((W.selectedWitness h).test.evalCyclic N (fun _ => x)) := by
        simp only [v, b, selectedMixed, selectedLower, replacedRankResidual, star_mul,
          Complex.star_def, Complex.conj_ofReal]
        ring
      simpa only [heq] using hc }
  exact ⟨j, V.exists_absorb_positive (W.replacedRankResidual h.val (c j)) (A j)
    (by linarith) ((hA j).mono le_rfl hqR)⟩

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

open VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem exists_native_frozen_rank_correlation (s a : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (h : W.shifts) (P : ℝ), 2 ≤ P → p ≤ P →
      ∀ M : ℕ, 0 < M → (M : ℝ) ≤ Real.exp P →
      ∀ ε ξ v γ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      ε * ξ * v * γ = W.family.orbit h.val →
      CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P + 2) ^ a)) ε.log →
      (∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
        (QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) x γ) : W.family.model.Space) =
        QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) y γ)) →
      Real.exp ((P + C) ^ C) ≤ N →
      ∃ y : ZMod N,
        (∀ x, ∑ i, ‖W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) ε (ξ * v) γ y x‖ ^ 2 = 1) ∧
        Nonempty (NativeVectorCorrelation (s - 1) N ((P + C) ^ C)
          (W.replacedRankResidual h.val (fun i x => W.family.model.frozenCyclicOrbitValue
            (W.family.vertical.observable i) ε (ξ * v) γ y x))) := by
  obtain ⟨c, _, hfreeze⟩ := exists_partition_orbit_freezing s a
  obtain ⟨b, _, hpart⟩ := exists_interval_residue_partition 1
  obtain ⟨C, hC, hbudget⟩ := exists_frozen_correlation_budget c b
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf h P hP hpP M hM hMP ε ξ v γ hprod hε hperiod hN
  classical
  let : NeZero M := ⟨hM.ne'⟩
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  have hP0 : 0 ≤ P := by linarith
  let D := (P + c) ^ c
  let L := D + 2 * P + 40
  let Q := P + (L + b) ^ b + 2
  let ρ := Real.exp (-L)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hPL : P ≤ L := by dsimp only [L]; linarith
  have hρ : 0 < ρ := Real.exp_pos _
  obtain ⟨hLC, hQC⟩ := hbudget P hP0
  have hlarge : Real.exp L ≤ N := (Real.exp_le_exp.mpr hLC).trans hN
  have hprec : 1 / ρ ≤ Real.exp ((L + 2) ^ 1) := by
    rw [pow_one]
    have he : 1 / ρ = Real.exp L := by simp only [ρ, Real.exp_neg, one_div, inv_inv]
    rw [he]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨n, hn, hcard, A, hA, hsum, hcells⟩ := hpart N M hL
    (hMP.trans (Real.exp_le_exp.mpr hPL)) hρ hprec
  have hqQ : (L + b) ^ b ≤ Q := by dsimp only [Q]; linarith
  have hQ : 2 ≤ Q := by
    have ht : 0 ≤ (L + b) ^ b := by positivity
    dsimp only [Q]
    linarith
  have hDgeom := W.family.complexity.1.mono W.family.model hpP
  have hprod' : ε * (ξ * v) * γ = W.family.orbit h.val := by
    simpa only [mul_assoc] using hprod
  obtain ⟨y, _, hmean⟩ := hfreeze W.family.model (by linarith : 1 ≤ P) hDgeom hρ A
    (fun j x => ((hA j).unit_interval x).1) hsum hcells
    (W.family.vertical.observable (W.selectedWitness h).coordinate.2) W.family.vertical.lipBound
    (W.family.vertical.norm _) (W.family.vertical.lipschitz _)
    (W.family.vertical.lip_bound.trans (Real.exp_le_exp.mpr hpP))
    ε (ξ * v) γ (W.family.orbit h.val) hprod' hε hperiod
  let B (j : Fin n × ZMod M) (i : Fin W.family.outputDim) (x : ZMod N) :=
    W.family.model.frozenCyclicOrbitValue (W.family.vertical.observable i) ε (ξ * v) γ (y j) x
  have herror : (𝔼 x, ‖W.selectedRank h x -
      ∑ j, (A j x : ℂ) * B j (W.selectedWitness h).coordinate.2 x‖) ≤ Real.exp (-(2 * p)) / 2 := by
    apply hmean.trans
    exact (frozen_correlation_precision_error P D hD (NeZero.pos N) hlarge).trans
      (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  obtain ⟨j, V⟩ := W.exists_rank_approximation_correlation hf h A B hQ
    (hcard.trans (Real.exp_le_exp.mpr hqQ))
    (fun j => (hA j).mono (by omega) hqQ) herror
  have hcost : productNiltestBudget (raisedNiltestBudget (p + Q + 2)) ≤ (P + C) ^ C :=
    (frozen_witness_budget_mono (by positivity) (by linarith)).trans hQC
  refine ⟨y j, fun x => W.family.vertical.unit _, ?_⟩
  exact ⟨(Classical.choice V).mono hcost⟩

end Erdos3

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)
  {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (E : RationalFilteredNilmanifold L s d) (T : E.DegreeRankStructure r)
  (hpq : p ≤ q) (hT : T.ComplexityLE q)
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

noncomputable def replacementFamily : NativeDegreeRankFamily s r (ZMod N) q where
  L := L
  dim := d
  model := E
  rank := T
  complexity := hT
  orbit := g
  normalized := hg
  outputDim := W.family.outputDim
  output_pos := W.family.output_pos
  output_bound := W.family.output_bound.trans (Real.exp_le_exp.mpr hpq)
  vertical := V

theorem replacementFamily_evalCyclic (i : Fin W.family.outputDim) (h x : ZMod N) :
    (W.replacementFamily E T hpq hT V g hg).evalCyclic N i h x =
      V.observable i (QuotientGroup.mk (E.filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (g h))) := rfl

theorem replacementFamily_residual (h : ZMod N) :
    nativeCorrelationResidual f (W.mixed.mono hpq)
        (W.replacementFamily E T hpq hT V g hg) h =
      W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (g h)))) := rfl

noncomputable def replaceRank (H : Finset (ZMod N)) (hne : H.Nonempty)
    (hdense : Real.exp (-q) * Fintype.card (ZMod N) ≤ (H.card : ℝ))
    (hcorr : ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N q
      (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (g h))))))) :
    NativeCorrelationStructure s r N q f where
  shifts := H
  nonempty := hne
  density := hdense
  mixed := W.mixed.mono hpq
  family := W.replacementFamily E T hpq hT V g hg
  correlation := hcorr

end Erdos3.NativeCorrelationStructure

end

end OAI
