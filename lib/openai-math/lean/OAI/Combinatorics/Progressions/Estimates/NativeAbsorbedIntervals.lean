import OAI.Combinatorics.Progressions.Dynamics.MixedQuadrupleBudget
import OAI.Combinatorics.Progressions.Estimates.MixedFixedReduction
import OAI.Combinatorics.Progressions.Geometry.NativeCoordinateErrorReduction
import OAI.Combinatorics.Progressions.Lattices.NativeRetainedIntegerMultilinearQuadruples
import OAI.Combinatorics.Progressions.Polynomial.IntervalSplitPolynomialBudget

namespace OAI

section

namespace Erdos3

structure NativeMultilinearIntervalFamily {s r N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℂ} (W : NativeCorrelationStructure s r N p f) (q : ℝ) where
  mixed : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) q
  mixed_dim : mixed.dim ≤ 2 ^ (s + 1) * W.mixed.dim
  mixed_symmetric : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
    mixed.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
      mixed.eval k x
  coordinate : Fin mixed.outputDim
  rankCoordinate : Fin W.family.outputDim
  weight : ZMod N → ℂ
  weight_norm : ∀ x, ‖weight x‖ ≤ 1
  shifts : Finset (ZMod N)
  shifts_subset : shifts ⊆ W.shifts
  shifts_nonempty : shifts.Nonempty
  shifts_short : CyclicShortShiftSet shifts
  shifts_density : Real.exp (-q) * Fintype.card (ZMod N) ≤ (shifts.card : ℝ)
  lower : NativeCrossWitnesses (s - 1) N q (fun x => f x * star (weight x)) f
    (fun h x => W.multilinearFactor mixed coordinate rankCoordinate h x.val) shifts
  quadruples : Finset (ZMod N × ZMod N × ZMod N)
  quadruples_nonempty : quadruples.Nonempty
  quadruples_density : Real.exp (-q) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (quadruples.card : ℝ)
  interval : ∀ t : quadruples, NativeIntegerQuadrupleWitness lower
    (W.multilinearFactor mixed coordinate rankCoordinate) q t

end Erdos3

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

noncomputable def intervalSet (t : B.quadruples) : Finset ℤ :=
  Finset.Ico ((B.interval t).start : ℤ) ((B.interval t).start + (B.interval t).length)

def delta (t : B.quadruples) : ℤ := cyclicBranchOffset t.val.1 (B.interval t).branch

def sample (t : B.quadruples) (n : ℤ) : Fin 5 → ℤ :=
  ![(t.val.2.1.val : ℤ), (t.val.2.1 - t.val.1).val, t.val.2.2.val, n, B.delta t]

noncomputable def rankProduct (t : B.quadruples) (n : ℤ) : ℂ :=
  fourPointProduct (W.family.eval B.rankCoordinate t.val.2.1)
    (W.family.eval B.rankCoordinate (t.val.2.1 - t.val.1))
    (W.family.eval B.rankCoordinate t.val.2.2)
    (W.family.eval B.rankCoordinate (t.val.2.2 - t.val.1)) (B.delta t) n

noncomputable def lowerProduct (t : B.quadruples) (n : ℤ) : ℂ :=
  fourPointProduct
    (B.lower.integerLower ⟨t.val.2.1, (B.interval t).first_mem⟩)
    (B.lower.integerLower ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩)
    (B.lower.integerLower ⟨t.val.2.2, (B.interval t).third_mem⟩)
    (B.lower.integerLower ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩) (B.delta t) n

noncomputable def residual (t : B.quadruples) (n : ℤ) : ℂ :=
  B.rankProduct t n * B.lowerProduct t n

theorem product_factorization (t : B.quadruples) (n : ℤ) :
    fourPointProduct
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.1, (B.interval t).first_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.2, (B.interval t).third_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩) (B.delta t) n =
    B.residual t n * translatedMixedProduct B.mixed (fun _ => B.coordinate)
      t.val.2.1.val (t.val.2.1 - t.val.1).val t.val.2.2.val (t.val.2.2 - t.val.1).val
      (B.delta t) n := by
  have h := B.lower.integerProduct_fourPoint_factorization
    (fun h n => B.mixed.eval B.coordinate (fun j => correlationInput (h.val : ℤ) n j.1))
    (W.family.eval B.rankCoordinate)
    ⟨t.val.2.1, (B.interval t).first_mem⟩
    ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩
    ⟨t.val.2.2, (B.interval t).third_mem⟩
    ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩ (B.delta t) n
  calc
    _ = translatedMixedProduct B.mixed (fun _ => B.coordinate)
        t.val.2.1.val (t.val.2.1 - t.val.1).val t.val.2.2.val (t.val.2.2 - t.val.1).val
        (B.delta t) n * B.rankProduct t n * B.lowerProduct t n := h
    _ = _ := by rw [residual]; ring

theorem mixed_correlation (t : B.quadruples) :
    Real.exp (-q) ≤ ‖𝔼 n ∈ B.intervalSet t,
      B.residual t n * translatedMixedProduct B.mixed (fun _ => B.coordinate)
        t.val.2.1.val (t.val.2.1 - t.val.1).val t.val.2.2.val (t.val.2.2 - t.val.1).val
        (B.delta t) n‖ := by
  have hc := (B.interval t).correlation
  change Real.exp (-q) ≤ ‖𝔼 n ∈ B.intervalSet t,
    fourPointProduct
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.1, (B.interval t).first_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.2, (B.interval t).third_mem⟩)
      (B.lower.integerProduct (W.multilinearFactor B.mixed B.coordinate B.rankCoordinate)
        ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩) (B.delta t) n‖ at hc
  simpa only [B.product_factorization] using hc

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3

theorem exists_native_multilinear_interval_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Nonempty (NativeMultilinearIntervalFamily W ((p + C) ^ C)) := by
  obtain ⟨C, hC, hquad⟩ := exists_integer_multilinear_quadruples s
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  obtain ⟨V, hdim, hsymm, k, i, weight, H, hweight, hsub, hH, hshort,
    hHsize, U, Q, hQ, hQsize, hinterval⟩ := hquad W hf
  classical
  have hdata (t : Q) := hinterval t.val t.property
  choose h₁ h₂ h₃ h₄ hrel hcyclic branch c len hlen hN hlenShort hcor hvol using hdata
  exact ⟨{
    mixed := V
    mixed_dim := hdim
    mixed_symmetric := hsymm
    coordinate := k
    rankCoordinate := i
    weight := weight
    weight_norm := hweight
    shifts := H
    shifts_subset := hsub
    shifts_nonempty := hH
    shifts_short := hshort
    shifts_density := hHsize
    lower := U
    quadruples := Q
    quadruples_nonempty := hQ
    quadruples_density := hQsize
    interval := fun t => {
      first_mem := h₁ t
      second_mem := h₂ t
      third_mem := h₃ t
      fourth_mem := h₄ t
      integer_relation := hrel t
      cyclic_correlation := hcyclic t
      branch := branch t
      start := c t
      length := len t
      length_pos := hlen t
      endpoint_le := hN t
      length_short := hlenShort t
      correlation := hcor t
      length_ratio := hvol t } }⟩

end Erdos3

end

section

namespace Erdos3

structure NativeRetainedMultilinearIntervalFamily {s r N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℂ} (W : NativeCorrelationStructure s r N p f) (q : ℝ)
    extends NativeMultilinearIntervalFamily W q where
  equivalence : NativeIntegerVectorEquivalence s q W.mixed.eval
    (fun k x => mixed.eval k (fun j => x j.1))

theorem exists_native_retained_multilinear_interval_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Nonempty (NativeRetainedMultilinearIntervalFamily W ((p + C) ^ C)) := by
  obtain ⟨C, hC, hquad⟩ := exists_integer_multilinear_quadruples_with_equivalence s
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  obtain ⟨V, hdim, hsymm, E, k, i, weight, H, hweight, hsub, hH, hshort,
    hHsize, U, Q, hQ, hQsize, hinterval⟩ := hquad W hf
  classical
  have hdata (t : Q) := hinterval t.val t.property
  choose h₁ h₂ h₃ h₄ hrel hcyclic branch c len hlen hN hlenShort hcor hvol using hdata
  exact ⟨{
    mixed := V
    mixed_dim := hdim
    mixed_symmetric := hsymm
    equivalence := E
    coordinate := k
    rankCoordinate := i
    weight := weight
    weight_norm := hweight
    shifts := H
    shifts_subset := hsub
    shifts_nonempty := hH
    shifts_short := hshort
    shifts_density := hHsize
    lower := U
    quadruples := Q
    quadruples_nonempty := hQ
    quadruples_density := hQsize
    interval := fun t => {
      first_mem := h₁ t
      second_mem := h₂ t
      third_mem := h₃ t
      fourth_mem := h₄ t
      integer_relation := hrel t
      cyclic_correlation := hcyclic t
      branch := branch t
      start := c t
      length := len t
      length_pos := hlen t
      endpoint_le := hN t
      length_short := hlenShort t
      correlation := hcor t
      length_ratio := hvol t } }⟩

end Erdos3

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

theorem intervalSet_nonempty (t : B.quadruples) : (B.intervalSet t).Nonempty := by
  refine ⟨((B.interval t).start : ℤ), Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩⟩
  exact lt_add_of_pos_right _ (Nat.cast_pos.mpr (B.interval t).length_pos)

theorem sample_update (t : B.quadruples) (n : ℤ) :
    B.sample t n = Function.update (B.sample t 0) (3 : Fin 5) n := by
  funext k
  fin_cases k <;> rfl

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

noncomputable def lowerProductExpansion {s r N : ℕ} [NeZero N] {p q : ℝ}
    {f : ZMod N → ℂ} {W : NativeCorrelationStructure s r N p f}
    (B : NativeMultilinearIntervalFamily W q) (t : B.quadruples) :
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (mixedErrorBudget (q + 2))
      (fun x => B.lowerProduct t (x ())) := by
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  let h : Fin 4 → B.shifts :=
    ![⟨t.val.2.1, (B.interval t).first_mem⟩,
      ⟨t.val.2.1 - t.val.1, (B.interval t).second_mem⟩,
      ⟨t.val.2.2, (B.interval t).third_mem⟩,
      ⟨t.val.2.2 - t.val.1, (B.interval t).fourth_mem⟩]
  let v (i : Fin 4) := B.lower.integerLower (h i)
  let E (i : Fin 4) : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (q + 2)
      (fun x => v i (x ())) :=
    NativeIntegerExpansion.ofTest (B.lower (h i)).test
      ((B.lower (h i)).complexity.mono (by linarith)) (fun _ => rfl)
  exact NativeIntegerExpansion.fourPoint v E (by linarith) (B.delta t)

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q P : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)

theorem reduce_mixed (D : NativeMixedReductionData B.mixed P) :
    ∃ (a : D.ReductionCode (fun _ => B.coordinate)) (R : Finset B.quadruples), R.Nonempty ∧
      Real.exp (-(q + 5 * P)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (R.card : ℝ) ∧
      ∀ t ∈ R, ∃ c : D.LowerCode a.translations (t.val.2.1 - t.val.1).val
          (t.val.2.2 - t.val.1).val (B.delta t),
        Real.exp (-(q + 7 * P)) ≤ ‖𝔼 n ∈ B.intervalSet t,
          B.residual t n * D.globalError (fun _ => B.coordinate) a (B.sample t n) *
            D.translationLower a.translations (t.val.2.1 - t.val.1).val
              (t.val.2.2 - t.val.1).val (B.delta t) c n‖ := by
  classical
  have hnonempty : (Finset.univ : Finset B.quadruples).Nonempty := by
    obtain ⟨t, ht⟩ := B.quadruples_nonempty
    exact ⟨⟨t, ht⟩, Finset.mem_univ _⟩
  obtain ⟨a, R, _, hR, hsize, hcor⟩ := D.reduce_family Finset.univ hnonempty
    B.intervalSet (fun _ n => n)
    (fun t => (t.val.2.1.val : ℤ)) (fun t => ((t.val.2.1 - t.val.1).val : ℤ))
    (fun t => (t.val.2.2.val : ℤ)) (fun t => ((t.val.2.2 - t.val.1).val : ℤ))
    B.delta (fun _ => B.coordinate) B.residual q
    (fun t _ => (B.interval t).integer_relation) (fun t _ => B.mixed_correlation t)
  refine ⟨a, R, hR, ?_, hcor⟩
  calc
    Real.exp (-(q + 5 * P)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
        Real.exp (-(5 * P)) * (Real.exp (-q) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(5 * P)) * (B.quadruples.card : ℝ) :=
      mul_le_mul_of_nonneg_left B.quadruples_density (Real.exp_nonneg _)
    _ ≤ (R.card : ℝ) := by simpa only [Finset.card_univ, Fintype.card_coe] using hsize

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3

open scoped BigOperators

structure NativeReducedIntervalFamily {s r N : ℕ} [NeZero N] {p q P : ℝ}
    {f : ZMod N → ℂ} {W : NativeCorrelationStructure s r N p f}
    (B : NativeMultilinearIntervalFamily W q) (D : NativeMixedReductionData B.mixed P)
    (K : ℝ) where
  base_budget : q ≤ K
  correlation_budget : q + 7 * P ≤ K
  global_budget : mixedErrorBudget P ≤ K
  lower_budget : mixedErrorPairBudget P ≤ K
  code : D.ReductionCode (fun _ => B.coordinate)
  retained : Finset B.quadruples
  retained_nonempty : retained.Nonempty
  density : Real.exp (-K) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (retained.card : ℝ)
  lowerChoice : ∀ t : retained,
    D.LowerCode code.translations (t.val.val.2.1 - t.val.val.1).val
      (t.val.val.2.2 - t.val.val.1).val (B.delta t.val)
  correlation : ∀ t : retained, Real.exp (-K) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
    B.residual t.val n * D.globalError (fun _ => B.coordinate) code (B.sample t.val n) *
      D.translationLower code.translations (t.val.val.2.1 - t.val.val.1).val
        (t.val.val.2.2 - t.val.val.1).val (B.delta t.val) (lowerChoice t) n‖

end Erdos3

end

section

namespace Erdos3.NativeMultilinearIntervalFamily

theorem reduce_with_budget {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)
    (D : NativeMixedReductionData B.mixed P) (hq : q ≤ K) (hc : q + 7 * P ≤ K)
    (hg : mixedErrorBudget P ≤ K) (hl : mixedErrorPairBudget P ≤ K) :
    Nonempty (NativeReducedIntervalFamily B D K) := by
  obtain ⟨a, R, hR, hsize, hcor⟩ := B.reduce_mixed D
  have hp : 0 ≤ P := le_trans (by norm_num) D.budget_two
  have hsize' : Real.exp (-K) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (R.card : ℝ) := by
    apply le_trans _ hsize
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.exp_le_exp.mpr
    linarith only [hp, hc]
  classical
  exact ⟨{
    base_budget := hq
    correlation_budget := hc
    global_budget := hg
    lower_budget := hl
    code := a
    retained := R
    retained_nonempty := hR
    density := hsize'
    lowerChoice := fun t => Classical.choose (hcor t.val t.property)
    correlation := fun t => (Real.exp_le_exp.mpr (neg_le_neg hc)).trans
      (Classical.choose_spec (hcor t.val t.property)) }⟩

end Erdos3.NativeMultilinearIntervalFamily

end

section

namespace Erdos3.NativeReducedIntervalFamily

open scoped BigOperators

variable {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
  {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K)

noncomputable def localLower (t : R.retained) (n : ℤ) : ℂ :=
  B.lowerProduct t.val n *
    D.translationLower R.code.translations (t.val.val.2.1 - t.val.val.1).val
      (t.val.val.2.2 - t.val.val.1).val (B.delta t.val) (R.lowerChoice t) n

noncomputable def globalExpansion :
    NativeIntegerExpansion (fun _ : Fin 5 => 1) s K
      (D.globalError (fun _ => B.coordinate) R.code) :=
  (D.globalErrorExpansion (fun _ => B.coordinate) R.code).mono R.global_budget

noncomputable def localExpansion (t : R.retained) :
    NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (intervalErrorBudget K)
      (fun x => R.localLower t (x ())) := by
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  have hK : 0 ≤ K := hq.trans R.base_budget
  have hbase := intervalErrorBaseBudget_bounds hK
  have hfirst : mixedErrorBudget (q + 2) ≤ intervalErrorBaseBudget K :=
    (mixedErrorBudget_mono (by linarith) (by linarith [R.base_budget])).trans hbase.2.2
  have hsecond : mixedErrorPairBudget P ≤ intervalErrorBaseBudget K :=
    R.lower_budget.trans hbase.2.1
  exact ((B.lowerProductExpansion t.val).mono hfirst).mul
    ((D.translationLowerExpansion R.code.translations (t.val.val.2.1 - t.val.val.1).val
      (t.val.val.2.2 - t.val.val.1).val (B.delta t.val) (R.lowerChoice t)).mono hsecond) hbase.1

theorem rank_correlation (t : R.retained) :
    Real.exp (-K) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
      B.rankProduct t.val n * D.globalError (fun _ => B.coordinate) R.code (B.sample t.val n) *
        R.localLower t n‖ := by
  simpa only [localLower, NativeMultilinearIntervalFamily.residual,
    mul_assoc, mul_left_comm, mul_comm] using R.correlation t

theorem interval_length_ratio (t : R.retained) :
    Real.exp (-K) ≤ ((B.interval t.val).length : ℝ) / N :=
  (Real.exp_le_exp.mpr (neg_le_neg R.base_budget)).trans (B.interval t.val).length_ratio

noncomputable def retainedTriples : Finset (ZMod N × ZMod N × ZMod N) :=
  R.retained.map ⟨Subtype.val, Subtype.val_injective⟩

theorem retainedTriples_card : R.retainedTriples.card = R.retained.card := by
  simp only [retainedTriples, Finset.card_map]

theorem retainedTriples_subset : R.retainedTriples ⊆ B.quadruples := by
  intro t ht
  obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp ht
  exact u.property

end Erdos3.NativeReducedIntervalFamily

end

section

namespace Erdos3

theorem exists_native_reduced_interval_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ (q : ℝ) (B : NativeMultilinearIntervalFamily W q) (P : ℝ)
        (D : NativeMixedReductionData B.mixed P),
        Nonempty (NativeReducedIntervalFamily B D ((p + C) ^ C)) := by
  obtain ⟨a, _, hfamily⟩ := exists_native_multilinear_interval_family s
  obtain ⟨b, _, hreduce⟩ := exists_mixed_quadruple_budget s
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Y + (Y + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 0 ≤ (q + b) ^ b := by positivity
  have hcost : q + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Y, q, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨B⟩ := hfamily W hf
  obtain ⟨P, ⟨D⟩, hP, hl, hg⟩ := hreduce B.mixed
  refine ⟨q, B, P, D, B.reduce_with_budget D ?_ ?_ ?_ ?_⟩
  · linarith only [hb, hcost]
  · linarith only [hP, hcost]
  · exact hg.trans (by linarith only [hq, hcost])
  · exact hl.trans (by linarith only [hq, hcost])

end Erdos3

end

section

namespace Erdos3.NativeReducedIntervalFamily

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_fixed_global_term {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
    {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K) :
    ∃ (j : Fin R.globalExpansion.count) (S : Finset R.retained), S.Nonempty ∧
      Real.exp (-(2 * K)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (S.card : ℝ) ∧
      ∀ t ∈ S, Real.exp (-(2 * K)) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
        B.rankProduct t.val n * (R.globalExpansion.test j).eval (B.sample t.val n) *
          R.localLower t n‖ := by
  classical
  let rel (t : R.retained) (_ : Unit) (j : Fin R.globalExpansion.count) : Prop :=
    Real.exp (-(2 * K)) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
      B.rankProduct t.val n * (R.globalExpansion.test j).eval (B.sample t.val n) * R.localLower t n‖
  have hnonempty : (Finset.univ : Finset R.retained).Nonempty := by
    obtain ⟨t, ht⟩ := R.retained_nonempty
    exact ⟨⟨t, ht⟩, Finset.mem_univ _⟩
  have hchoice : ∀ t ∈ (Finset.univ : Finset R.retained), ∀ b, ∃ j, rel t b j := by
    intro t _ _
    have hc : Real.exp (-K) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
        (B.rankProduct t.val n * R.localLower t n) *
          D.globalError (fun _ => B.coordinate) R.code (B.sample t.val n)‖ := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using R.rank_correlation t
    obtain ⟨j, hj⟩ := R.globalExpansion.select_sample_product_correlation
      (B.intervalSet t.val) (B.sample t.val) (fun n => B.rankProduct t.val n * R.localLower t n) hc
    refine ⟨j, ?_⟩
    rw [show K + K = 2 * K by ring] at hj
    simpa only [rel, mul_assoc, mul_left_comm, mul_comm] using hj
  have hcount : (Fintype.card (Fin R.globalExpansion.count) : ℝ) ≤ Real.exp K := by
    simpa only [Fintype.card_fin] using R.globalExpansion.count_bound
  obtain ⟨j, S, _, hS, hsize, hfixed⟩ :=
    exists_large_fixed_choices Finset.univ hnonempty rel hchoice hcount
  refine ⟨j (), S, hS, ?_, fun t ht => hfixed t ht ()⟩
  calc
    Real.exp (-(2 * K)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
        Real.exp (-K) * (Real.exp (-K) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-K) * (R.retained.card : ℝ) :=
      mul_le_mul_of_nonneg_left R.density (Real.exp_nonneg _)
    _ ≤ (S.card : ℝ) := by
      simpa only [Fintype.card_unit, Nat.cast_one, mul_one, Finset.card_univ, Fintype.card_coe] using hsize

end Erdos3.NativeReducedIntervalFamily

end

section

namespace Erdos3

namespace NativeMultilinearIntervalFamily

theorem rankProduct_norm {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)
    (t : B.quadruples) (n : ℤ) : ‖B.rankProduct t n‖ ≤ 1 := by
  simp only [rankProduct, fourPointProduct, norm_mul, norm_star]
  calc
    _ ≤ (1 : ℝ) * 1 * 1 * 1 := by
      gcongr <;> exact W.family.norm_eval _ _ _
    _ = 1 := by norm_num

end NativeMultilinearIntervalFamily

namespace NativeReducedIntervalFamily

variable {s r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
  {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K)

theorem localLower_norm (t : R.retained) (n : ℤ) :
    ‖R.localLower t n‖ ≤ Real.exp (2 * intervalErrorBudget K) :=
  (R.localExpansion t).norm_eval_le (fun _ => n)

theorem scalar_norm (t : R.retained) (n : ℤ) :
    ‖B.rankProduct t.val n * R.localLower t n‖ ≤ Real.exp (2 * intervalErrorBudget K) := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul (B.rankProduct_norm t.val n) (R.localLower_norm t n)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

end NativeReducedIntervalFamily

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def IntervalGlobalReductionStatement (s c : ℕ) : Prop :=
  ∀ {r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
    {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K),
    ∃ (weight : ℤ → ℂ) (Q : Finset R.retained), (∀ n, ‖weight n‖ ≤ 1) ∧ Q.Nonempty ∧
      Real.exp (-(2 * K + intervalSplitTermBudget c K)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤
        (Q.card : ℝ) ∧
      ∀ t ∈ Q, ∃ v : ℤ → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) (intervalSplitLocalBudget c K)
          (fun x => v (x ()))) ∧
        Real.exp (-intervalSplitTermBudget c K) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
          B.rankProduct t.val n * weight n * v n‖

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_interval_global_reduction (s : ℕ) :
    ∃ c : ℕ, 2 ≤ c ∧ IntervalGlobalReductionStatement s c := by
  obtain ⟨c, hc, hreduce⟩ := exists_coordinate_error_reduction (Fin 5) s
  refine ⟨c, hc, ?_⟩
  intro r N _ p q P K f W B D R
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  have hK : 0 ≤ K := hq.trans R.base_budget
  have hinput := intervalSplitInput_bounds hK
  have hinput0 : 0 ≤ intervalSplitInput K := le_trans (by norm_num) hinput.1
  obtain ⟨j, S, hS, hSsize, hcorr⟩ := R.exists_fixed_global_term
  let T := R.globalExpansion.test j
  let F (t : R.retained) (n : ℤ) := B.rankProduct t.val n * R.localLower t n
  have hT : T.ComplexityLE (intervalSplitInput K) :=
    (R.globalExpansion.complexity j).mono hinput.2.1
  have hF : ∀ t ∈ S, ∀ n ∈ B.intervalSet t.val, ‖F t n‖ ≤ Real.exp (intervalSplitInput K) := by
    intro t _ n _
    exact (R.scalar_norm t n).trans (Real.exp_le_exp.mpr hinput.2.2.2)
  have hcorr' : ∀ t ∈ S, Real.exp (-intervalSplitInput K) ≤
      ‖𝔼 n ∈ B.intervalSet t.val, F t n * T.eval
        (Function.update (B.sample t.val 0) (3 : Fin 5) n)‖ := by
    intro t ht
    have h := (Real.exp_le_exp.mpr (neg_le_neg hinput.2.2.1)).trans (hcorr t ht)
    simpa only [F, T, ← B.sample_update, mul_assoc, mul_left_comm, mul_comm] using h
  obtain ⟨weight, Q, hw, _, hQ, hQsize, hcor⟩ := hreduce (3 : Fin 5) T hinput.1 hT S hS
    (fun t => B.intervalSet t.val) (fun t => B.sample t.val 0) (fun _ n => n) F
    (fun t _ => B.intervalSet_nonempty t.val) hF hcorr'
  refine ⟨weight, Q, hw, hQ, ?_, ?_⟩
  · calc
      Real.exp (-(2 * K + intervalSplitTermBudget c K)) * (Fintype.card (ZMod N) : ℝ) ^ 3 =
          Real.exp (-intervalSplitTermBudget c K) *
            (Real.exp (-(2 * K)) * (Fintype.card (ZMod N) : ℝ) ^ 3) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-intervalSplitTermBudget c K) * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_left hSsize (Real.exp_nonneg _)
      _ ≤ (Q.card : ℝ) := hQsize
  · intro t ht
    obtain ⟨v, _, ⟨E⟩, hcv⟩ := hcor t ht
    let w (n : ℤ) := R.localLower t n * v n
    have hL : 0 ≤ intervalErrorBudget K := intervalErrorBudget_nonneg hK
    have hJ : 0 ≤ intervalSplitTermBudget c K := by
      unfold intervalSplitTermBudget
      positivity
    have hL' : intervalErrorBudget K ≤ intervalErrorBudget K + intervalSplitTermBudget c K + 2 := by
      linarith only [hJ]
    have hJ' : intervalSplitTermBudget c K ≤ intervalErrorBudget K + intervalSplitTermBudget c K + 2 := by
      linarith only [hL]
    have htwo : 2 ≤ intervalErrorBudget K + intervalSplitTermBudget c K + 2 := by
      linarith only [hL, hJ]
    refine ⟨w, ⟨?_⟩, ?_⟩
    · exact ((R.localExpansion t).mono hL').mul (E.mono hJ') htwo
    · simpa only [F, w, intervalSplitTermBudget, mul_assoc, mul_left_comm, mul_comm] using hcv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_absorbed_interval_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p q P K : ℝ} {f : ZMod N → ℂ}
      {W : NativeCorrelationStructure s r N p f} {B : NativeMultilinearIntervalFamily W q}
      {D : NativeMixedReductionData B.mixed P} (R : NativeReducedIntervalFamily B D K),
      ∃ (weight : ℤ → ℂ) (Q : Finset R.retained), (∀ n, ‖weight n‖ ≤ 1) ∧ Q.Nonempty ∧
        Real.exp (-((K + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, ∃ v : ℤ → ℂ,
          Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((K + C) ^ C)
            (fun x => v (x ()))) ∧
          Real.exp (-((K + C) ^ C)) ≤ ‖𝔼 n ∈ B.intervalSet t.val,
            B.rankProduct t.val n * weight n * v n‖ := by
  obtain ⟨c, _, hreduce⟩ := exists_interval_global_reduction s
  obtain ⟨C, hC, hbudget⟩ := exists_interval_split_budget c
  refine ⟨C, hC, ?_⟩
  intro r N _ p q P K f W B D R
  have hq : 0 ≤ q := (Nat.cast_nonneg B.mixed.dim).trans B.mixed.complexity.1.1
  have hK : 0 ≤ K := hq.trans R.base_budget
  obtain ⟨weight, Q, hw, hQ, hsize, hcor⟩ := hreduce R
  have hF : intervalSplitTermBudget c K ≤ (K + C) ^ C := by
    linarith only [hK, (hbudget K hK).1]
  refine ⟨weight, Q, hw, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg (hbudget K hK).1)) (by positivity)).trans hsize
  · intro t ht
    obtain ⟨v, ⟨E⟩, hc⟩ := hcor t ht
    exact ⟨v, ⟨E.mono (hbudget K hK).2⟩, (Real.exp_le_exp.mpr (neg_le_neg hF)).trans hc⟩

end Erdos3

end

end OAI
