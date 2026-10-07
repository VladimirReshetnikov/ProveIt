/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CubicSevenCornerSymmetry
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerThirds
import OAI.Combinatorics.Progressions.Linear.CubicKernelCorrelation

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicPairComponent (out : Fin W.outputDim × Fin W.outputDim)
    (h y k : Fin 3) (shift : ℤ) : W.model.Niltest (fun _ : Fin 3 => 1) :=
  ((W.tensorPower 2).component ((tensorIndexEquiv W.outputDim 2) ![out.1, out.2])).affinePullback
    (fun j l => if l = (if j.1 = 0 then h else if j.2.val = 0 then y else k) then 1 else 0)
    (fun j => if j.1 = 0 then 0 else if j.2.val = 0 then 0 else shift)

theorem cubicPairComponent_eval (out : Fin W.outputDim × Fin W.outputDim)
    (h y k : Fin 3) (shift : ℤ) (n : Fin 3 → ℤ) :
    (W.cubicPairComponent out h y k shift).eval n =
      W.eval out.1 (cubicTrilinearInput (n h) (n y) (n k + shift)) *
        W.eval out.2 (cubicTrilinearInput (n h) (n y) (n k + shift)) := by
  let A : CubicReplicatedIndex → Fin 3 → ℤ := fun j l =>
    if l = (if j.1 = 0 then h else if j.2.val = 0 then y else k) then 1 else 0
  let b : CubicReplicatedIndex → ℤ := fun j =>
    if j.1 = 0 then 0 else if j.2.val = 0 then 0 else shift
  have hinput : integerAffineMap A b n = cubicTrilinearInput (n h) (n y) (n k + shift) := by
    funext j
    rcases j with ⟨j, a⟩
    fin_cases j <;> fin_cases a <;>
      simp [A, b, integerAffineMap, cubicTrilinearInput, ite_mul, add_comm]
  calc
    _ = ((W.tensorPower 2).component ((tensorIndexEquiv W.outputDim 2) ![out.1, out.2])).eval
        (integerAffineMap A b n) :=
      Niltest.eval_affinePullback _ A b n
    _ = (W.tensorPower 2).eval ((tensorIndexEquiv W.outputDim 2) ![out.1, out.2])
        (integerAffineMap A b n) := (W.tensorPower 2).component_eval _ _
    _ = ∏ a, W.eval ((tensorIndexEquiv W.outputDim 2).symm
        ((tensorIndexEquiv W.outputDim 2) ![out.1, out.2]) a) (integerAffineMap A b n) :=
      W.tensorPower_eval 2 _ _
    _ = _ := by
      rw [Equiv.symm_apply_apply, Fin.prod_univ_two, hinput]
      rfl

theorem cubicPairComponent_complexity (out : Fin W.outputDim × Fin W.outputDim)
    (h y k : Fin 3) (shift : ℤ) :
    (W.cubicPairComponent out h y k shift).ComplexityLE (tensorPowerBudget 2 p + 4) :=
  (W.tensorPower 2).component_complexity ((tensorIndexEquiv W.outputDim 2) ![out.1, out.2])

theorem cubicPairComponent_vertical (out : Fin W.outputDim × Fin W.outputDim)
    (h y k : Fin 3) (shift : ℤ) (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
    (x : W.model.Space) :
    (W.cubicPairComponent out h y k shift).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (2 • W.vertical.frequency) z.coord : ℝ) : CircleFourier.Circle) *
          (W.cubicPairComponent out h y k shift).observable x := by
  exact (W.tensorPower 2).vertical.vertical ((tensorIndexEquiv W.outputDim 2) ![out.1, out.2])
    z (by
      change z ∈ W.multi.realSubgroup (fun _ : CubicReplicatedIndex => 1)
      rwa [W.multi.realSubgroup_top]) x

theorem cubicPairComponent_orbit_eq (out out' : Fin W.outputDim × Fin W.outputDim)
    (h y k : Fin 3) (shift : ℤ) :
    (W.cubicPairComponent out h y k shift).orbit =
      (W.cubicPairComponent out' h y k shift).orbit := rfl

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicOriginalComponent (out : Fin W.outputDim)
    (h y k : Fin 3) (shift : ℤ) : W.model.Niltest (fun _ : Fin 3 => 1) :=
  (W.component out).affinePullback
    (fun j l => if l = (if j.1 = 0 then h else if j.2.val = 0 then y else k) then 1 else 0)
    (fun j => if j.1 = 0 then 0 else if j.2.val = 0 then 0 else shift)

theorem cubicOriginalComponent_eval (out : Fin W.outputDim)
    (h y k : Fin 3) (shift : ℤ) (n : Fin 3 → ℤ) :
    (W.cubicOriginalComponent out h y k shift).eval n =
      W.eval out (cubicTrilinearInput (n h) (n y) (n k + shift)) := by
  let A : CubicReplicatedIndex → Fin 3 → ℤ := fun j l =>
    if l = (if j.1 = 0 then h else if j.2.val = 0 then y else k) then 1 else 0
  let b : CubicReplicatedIndex → ℤ := fun j =>
    if j.1 = 0 then 0 else if j.2.val = 0 then 0 else shift
  have hinput : integerAffineMap A b n = cubicTrilinearInput (n h) (n y) (n k + shift) := by
    funext j
    rcases j with ⟨j, a⟩
    fin_cases j <;> fin_cases a <;>
      simp [A, b, integerAffineMap, cubicTrilinearInput, ite_mul, add_comm]
  calc
    _ = (W.component out).eval (integerAffineMap A b n) :=
      Niltest.eval_affinePullback _ A b n
    _ = W.eval out (integerAffineMap A b n) := W.component_eval _ _
    _ = _ := congrArg (W.eval out) hinput

theorem cubicOriginalComponent_complexity (out : Fin W.outputDim)
    (h y k : Fin 3) (shift : ℤ) :
    (W.cubicOriginalComponent out h y k shift).ComplexityLE (p + 4) :=
  W.component_complexity out

theorem cubicOriginalComponent_vertical (out : Fin W.outputDim)
    (h y k : Fin 3) (shift : ℤ) (z : W.model.RealGroup)
    (hz : z ∈ W.model.filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
    (x : W.model.Space) :
    (W.cubicOriginalComponent out h y k shift).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency z.coord : ℝ) : CircleFourier.Circle) *
          (W.cubicOriginalComponent out h y k shift).observable x := by
  exact W.vertical.vertical out
    z (by
      change z ∈ W.multi.realSubgroup (fun _ : CubicReplicatedIndex => 1)
      rwa [W.multi.realSubgroup_top]) x

theorem cubicOriginalComponent_orbit_pair (out : Fin W.outputDim)
    (pair : Fin W.outputDim × Fin W.outputDim) (h y k : Fin 3) (shift : ℤ) :
    (W.cubicOriginalComponent out h y k shift).orbit =
      (W.cubicPairComponent pair h y k shift).orbit := rfl

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

def cubicPairBudget (p q : ℝ) : ℝ := 4 * (p + q + 1) + raisedNiltestBudget (p + q) + 6

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
  {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  (V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift)))

abbrev CubicPairAlgebra := ∀ k : Option (Fin 2), optionLieSpace V.L (fun _ : Fin 2 => W.L) k

noncomputable def cubicPairModels : ∀ k : Option (Fin 2),
    RationalFilteredNilmanifold (optionLieSpace V.L (fun _ : Fin 2 => W.L) k)
      (∑ _ : CubicReplicatedIndex, 1) (optionDimension V.dim (fun _ : Fin 2 => W.dim) k) :=
  optionFactors (V.model.raiseStep (by decide)) (fun _ : Fin 2 => W.model)

noncomputable def cubicPairTests :
    ∀ k, (V.cubicPairModels k).Niltest (fun _ : Fin 3 => 1)
  | none => (V.test.raiseStep (by decide)).conjugate
  | some k => ![(W.cubicPairComponent i 1 2 0 shift).conjugate,
      W.cubicPairComponent j 2 1 0 shift] k

noncomputable def cubicPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => W.L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![-(2 • W.vertical.frequency), 2 • W.vertical.frequency] k

theorem cubicPairTests_eval (n : Fin 3 → ℤ) :
    (∏ k, (V.cubicPairTests k).eval n) =
      W.cubicAntisymmetricPair i j (n 1) (n 2) (n 0 + shift) * star (V.test.eval n) := by
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change (V.test.raiseStep (by decide : 2 ≤ ∑ _ : CubicReplicatedIndex, 1)).conjugate.eval n *
    ((W.cubicPairComponent i 1 2 0 shift).conjugate.eval n *
      (W.cubicPairComponent j 2 1 0 shift).eval n) = _
  rw [Niltest.eval_conjugate, Niltest.raiseStep_eval, Niltest.eval_conjugate,
    W.cubicPairComponent_eval, W.cubicPairComponent_eval]
  simp only [NativeMultidegreeNilcharacter.cubicAntisymmetricPair, star_mul]
  ring

theorem cubicPairTests_vertical (k : Option (Fin 2))
    (z : (V.cubicPairModels k).RealGroup)
    (hz : z ∈ (V.cubicPairModels k).filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
    (x : (V.cubicPairModels k).Space) :
    (V.cubicPairTests k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.cubicPairFrequencies k) z.coord : ℝ) : CircleFourier.Circle) *
          (V.cubicPairTests k).observable x := by
  cases k with
  | none =>
    exact V.test.conjugate.raiseStep_top_vertical
      (by decide : 2 < ∑ _ : CubicReplicatedIndex, 1) z hz x
  | some k =>
    fin_cases k
    · exact Niltest.conjugate_vertical _ _ (W.cubicPairComponent_vertical i 1 2 0 shift) z hz x
    · exact W.cubicPairComponent_vertical j 2 1 0 shift z hz x

include V in
theorem cubicPairBudget_six_le : 6 ≤ cubicPairBudget p q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  unfold cubicPairBudget raisedNiltestBudget
  nlinarith [sq_nonneg (p + q + 2)]

theorem cubicPairTests_complexity (k : Option (Fin 2)) :
    (V.cubicPairTests k).ComplexityLE (cubicPairBudget p q) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hpq : 0 ≤ p + q := add_nonneg hp hq
  have hr : 0 ≤ raisedNiltestBudget (p + q) := hpq.trans (le_raisedNiltestBudget _)
  cases k with
  | none =>
    exact (V.test.raiseStep_complexity (by decide) hpq
      (V.complexity.mono (le_add_of_nonneg_left hp))).mono
        (by unfold cubicPairBudget; linarith)
  | some k =>
    have hcost : tensorPowerBudget 2 p + 4 ≤ cubicPairBudget p q := by
      unfold cubicPairBudget tensorPowerBudget
      norm_num
      linarith
    fin_cases k
    · exact (W.cubicPairComponent_complexity i 1 2 0 shift).mono hcost
    · exact (W.cubicPairComponent_complexity j 2 1 0 shift).mono hcost

end NativeSampleCorrelation
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_cubic_integer_translation_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      (a b : CubicReplicatedIndex → ℤ),
      NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
        (fun i x => W.eval i (x + a)) (fun i x => W.eval i (x + b)) := by
  obtain ⟨C, hC, htranslate⟩ :=
    UnitVerticalObservable.exists_integer_translation_equivalence_budget 2
  refine ⟨C, hC, ?_⟩
  intro p W a b
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let U : W.model.UnitVerticalObservable
      (W.model.filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
      (Fin W.outputDim) p :=
    { W.vertical with
      vertical := fun i z hz x => W.vertical.vertical i z (W.multi.realSubgroup_top.symm ▸ hz) x
      integral := fun z hz hL => W.vertical.integral z (W.multi.realSubgroup_top.symm ▸ hz) hL }
  have hI : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have E := htranslate W.model U (W.multi.orbitToOrdinary W.orbit) hp W.complexity.1 hI a b
  have heval (i : Fin W.outputDim) (x : CubicReplicatedIndex → ℤ) :
      U.observable i (QuotientGroup.mk
        (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1) x
          (W.multi.orbitToOrdinary W.orbit))) = W.eval i x := by
    rw [W.multi.orbitToOrdinary_eval]
    rfl
  have hl : (fun i x => U.observable i (QuotientGroup.mk
      (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1) (x + a)
        (W.multi.orbitToOrdinary W.orbit)))) = (fun i x => W.eval i (x + a)) := by
    funext i x
    exact heval i (x + a)
  have hr : (fun i x => U.observable i (QuotientGroup.mk
      (W.model.filtration.realification.polynomialOrbitEval (fun _ => 1) (x + b)
        (W.multi.orbitToOrdinary W.orbit)))) = (fun i x => W.eval i (x + b)) := by
    funext i x
    exact heval i (x + b)
  exact (congrArg₂ (fun f g : Fin W.outputDim → (CubicReplicatedIndex → ℤ) → ℂ =>
    NativeIntegerVectorEquivalence 2 ((p + C) ^ C) f g) hl hr).mp E

theorem exists_cubic_shifted_diagonal_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p) (shift : ℤ),
      NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
        (fun out (x : Fin 2 → ℤ) => W.eval out (fun j => x j.1))
        (fun out x => W.eval out (cubicTrilinearInput (x 0) (x 1) (x 1 + shift))) := by
  obtain ⟨C, hC, htranslate⟩ := exists_cubic_integer_translation_equivalence
  refine ⟨C, hC, ?_⟩
  intro p W shift
  let b : CubicReplicatedIndex → ℤ := fun j =>
    if j.1 = 0 then 0 else if j.2.val = 0 then 0 else shift
  have E := (htranslate W 0 b).coordinatePullback (fun j => j.1)
  have hleft : (fun out (x : Fin 2 → ℤ) => W.eval out ((fun j => x j.1) + 0)) =
      (fun out x => W.eval out (fun j => x j.1)) := by
    funext out x
    rw [add_zero]
  have hright : (fun out (x : Fin 2 → ℤ) => W.eval out ((fun j => x j.1) + b)) =
      (fun out x => W.eval out (cubicTrilinearInput (x 0) (x 1) (x 1 + shift))) := by
    funext out x
    apply congrArg (W.eval out)
    funext j
    rcases j with ⟨j, k⟩
    fin_cases j <;> fin_cases k <;> simp [b, Pi.add_apply, cubicTrilinearInput]
  simpa only [hleft, hright] using E

theorem exists_cubic_mixed_shifted_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) p)
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) q),
      0 ≤ r → NativeIntegerVectorEquivalence 2 r M.eval (fun out x => W.eval out (fun j => x j.1)) →
      ∀ shift : ℤ, NativeIntegerVectorEquivalence 2 ((q + r + C) ^ C)
        M.eval (fun out x => W.eval out (cubicTrilinearInput (x 0) (x 1) (x 1 + shift))) := by
  obtain ⟨a, _, hshift⟩ := exists_cubic_shifted_diagonal_equivalence
  obtain ⟨b, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  let U := X + (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((U + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p q r M W hr E shift
  have hq : 0 ≤ q := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let u := (q + r) + (q + r + a) ^ a
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hru : r ≤ u := by dsimp [u]; linarith [pow_nonneg (by positivity : 0 ≤ q + r + a) a]
  have hau : (q + a) ^ a ≤ u := by
    apply le_trans _ (le_add_of_nonneg_left (add_nonneg hq hr))
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hcost : (u + b) ^ b ≤ (q + r + C) ^ C := by
    simpa [X, U, u, Polynomial.eval₂_pow] using hbudget (q + r) (add_nonneg hq hr)
  exact (htrans hu (E.mono hru) ((hshift W shift).mono hau)
    (fun x => W.unit_eval _)).mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

noncomputable def cubicRoot {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p) :
    NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) (tensorPowerBudget 9 p) :=
  (W.rationalDilation (1 / 3)).tensorPower 9

theorem cubicRoot_dim {p : ℝ}
    (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p) :
    W.cubicRoot.dim = W.dim := rfl

theorem exists_explicit_cubic_root_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p),
      NativeIntegerVectorEquivalence 2 ((p + C) ^ C) W.eval (tensorVector W.cubicRoot.eval 3) := by
  have hsum : (∑ _ : CubicReplicatedIndex, 1) = (3 : ℕ) := by decide
  have hpos : 1 ≤ ∑ _ : CubicReplicatedIndex, 1 := by rw [hsum]; norm_num
  obtain ⟨A, _, hdilation⟩ :=
    exists_dilation_degree_equivalence (fun _ : CubicReplicatedIndex => 1) hpos 3
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 30 * (X + 1) + X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hA : 0 ≤ (p + A) ^ A := by positivity
  have hbound : (p + A) ^ A + 30 * (p + 1) + p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by linarith
  have hAr : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  have hdimBound : 3 * tensorPowerBudget 9 p ≤ (p + C) ^ C := by
    norm_num [tensorPowerBudget]
    linarith
  let V := W.rationalDilation (1 / 3)
  let R := V.tensorPower 9
  have hleft (i : Fin W.outputDim) (x : CubicReplicatedIndex → ℤ) :
      W.eval i x = integerDilationVector V.eval 3 i x :=
    (W.rationalDilation_eval_rescaled (1 / 3) 3 (by norm_num) i x).symm
  have hright (b : Fin 3 → Fin R.outputDim) (x : CubicReplicatedIndex → ℤ) :
      tensorVector R.eval 3 b x =
        signedTensorVector V.eval ((3 : ℤ) ^ ∑ _ : CubicReplicatedIndex, 1)
          (rootTensorIndex W.outputDim 3 (∑ _ : CubicReplicatedIndex, 1) hpos b) x := by
    exact V.tensorPower_tensor_eval 3 (∑ _ : CubicReplicatedIndex, 1) hpos b x
  have hdim : (Fintype.card (Fin 3 → Fin R.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ Real.exp (tensorPowerBudget 9 p) ^ 3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) R.output_bound _
      _ = Real.exp (3 * tensorPowerBudget 9 p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (tensorPowerBudget 9 p) 3).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdimBound
  have E := (hdilation V).of_coordinate_maps W.eval (tensorVector R.eval 3) id
    (rootTensorIndex W.outputDim 3 (∑ _ : CubicReplicatedIndex, 1) hpos) hleft hright
    (by simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpr)) hdim hAr
  change NativeIntegerVectorEquivalence 2 ((p + C) ^ C) W.eval (tensorVector R.eval 3)
  simpa only [hsum, Nat.reduceSub] using E

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicCyclicDiagonalDerivative {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) : ℂ :=
  W.eval a.1 (fun _ => ((x 1).val : ℤ)) *
    star (W.eval a.2 (fun _ => ((x 0 + x 1).val : ℤ)))

noncomputable def cubicWrappedDiagonalDerivative (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  W.eval a.1 (fun _ => x 1) * star (W.eval a.2 (fun _ => x 1 + x 0 - N))

noncomputable def cubicDiagonalWrapCoefficient (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ℂ :=
  W.eval k (fun _ => x 1 + x 0) * star (W.eval j (fun _ => x 1 + x 0 - N))

theorem cubicWrappedDiagonalDerivative_norm (N : ℕ) (a : Fin W.outputDim × Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.cubicWrappedDiagonalDerivative N a x‖ ≤ 1 := by
  simp only [cubicWrappedDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
    (W.norm_eval _ _)

theorem cubicDiagonalWrapCoefficient_norm (N : ℕ) (j k : Fin W.outputDim)
    (x : Fin 2 → ℤ) : ‖W.cubicDiagonalWrapCoefficient N j k x‖ ≤ 1 := by
  simp only [cubicDiagonalWrapCoefficient, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
    (W.norm_eval _ _)

theorem cubicWrappedDiagonalDerivative_resolution (N : ℕ)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.cubicWrappedDiagonalDerivative N a x =
      ∑ k, W.cubicDiagonalWrapCoefficient N a.2 k x * W.cubicDiagonalDerivative (a.1, k) x := by
  have h := complex_unit_vector_resolution
    (fun k => W.eval k (fun _ => x 1 + x 0)) (W.unit_eval _)
    (star (W.eval a.2 (fun _ => x 1 + x 0 - N)))
  calc
    _ = W.eval a.1 (fun _ => x 1) *
        ∑ k, (star (W.eval a.2 (fun _ => x 1 + x 0 - N)) *
          star (W.eval k (fun _ => x 1 + x 0))) * W.eval k (fun _ => x 1 + x 0) := by
      rw [← h]
      rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [cubicDiagonalWrapCoefficient, cubicDiagonalDerivative]
      ring

theorem cubicCyclicDiagonalDerivative_branches {N : ℕ} [NeZero N]
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    W.cubicCyclicDiagonalDerivative a x =
      (1 - (cyclicCarry (x 0) (x 1) : ℂ)) *
          W.cubicDiagonalDerivative a (fun z => ((x z).val : ℤ)) +
        (cyclicCarry (x 0) (x 1) : ℂ) *
          W.cubicWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) := by
  have hval := cyclic_representative_add (x 0) (x 1)
  have hlt := (x 0).val_lt
  by_cases hw : N ≤ (x 0).val + (x 1).val
  · have hcut : N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_true, Complex.ofReal_one, sub_self, zero_mul, one_mul, zero_add,
      cubicCyclicDiagonalDerivative, cubicWrappedDiagonalDerivative]
    rw [hval, ite_eq_left hcut]
  · have hcut : ¬N - (x 0).val ≤ (x 1).val := by omega
    simp only [cyclicCarry, hw, ite_false, Complex.ofReal_zero, sub_zero, zero_mul, one_mul, add_zero,
      cubicCyclicDiagonalDerivative, cubicDiagonalDerivative]
    rw [hval, ite_eq_right hcut, sub_zero]

theorem exists_cubicDiagonalWrapCoefficient_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p) (N : ℕ)
      (j k : Fin W.outputDim),
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 ((p + C) ^ C)
        (W.cubicDiagonalWrapCoefficient N j k)) := by
  obtain ⟨C, hC, htranslate⟩ := exists_cubic_integer_translation_equivalence
  refine ⟨C, hC, ?_⟩
  intro p W N j k
  let A : CubicReplicatedIndex → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1 + x 0, map_zero' := by simp,
      map_add' := fun x y => by simp only [Pi.add_apply]; ring }
  obtain ⟨F⟩ := (htranslate W 0 (fun _ => -(N : ℤ))).expansion k j
  have H := F.linearPullbackHom A
  have heq : (fun x : Fin 2 → ℤ => W.eval k ((fun l => A l x) + 0) *
      star (W.eval j ((fun l => A l x) + fun _ => -(N : ℤ)))) =
      W.cubicDiagonalWrapCoefficient N j k := by
    funext x
    simp only [add_zero, cubicDiagonalWrapCoefficient, sub_eq_add_neg]
    rfl
  exact ⟨heq ▸ H⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem third_dilation_integer_representative {σ : Type*} [Fintype σ]
    {bound : σ → ℕ} {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
    (x : σ → ℤ) (j : Fin W.outputDim) :
    (W.rationalDilation (1 / 3)).eval j (fun i => x i - ((x i : ZMod 3).val : ℤ)) =
      W.eval j (fun i => x i / 3) := by
  have hx : (fun i => x i - ((x i : ZMod 3).val : ℤ)) = (fun i => 3 * (x i / 3)) := by
    funext i
    rw [ZMod.val_intCast]
    omega
  rw [hx]
  exact W.rationalDilation_eval_rescaled (1 / 3) 3 (by norm_num) j _

theorem exists_cubic_third_dilation_pattern_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
      (a b c : Fin 2),
      NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
        (fun j (x : Fin 2 → ℤ) =>
          (W.rationalDilation (1 / 3)).eval j (cubicTrilinearInput (x a) (x b) (x c)))
        (fun j x => W.eval j (cubicTrilinearInput (x a / 3) (x b / 3) (x c / 3))) := by
  obtain ⟨A, _, hshift⟩ := exists_cubic_integer_translation_equivalence
  obtain ⟨B, _, hresidue⟩ := exists_pairThirdIndicator_expansion
  obtain ⟨D, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A + Polynomial.C B + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C D) ^ D + T + 9)
  refine ⟨C, hC, ?_⟩
  intro p W a b c
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let V := W.rationalDilation (1 / 3)
  let t : ℝ := (p + A) ^ A + B + p + 2
  have ha : 0 ≤ (p + A) ^ A := by positivity
  have hb : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have hat : (p + A) ^ A ≤ t := by dsimp [t]; linarith
  have hbt : (B : ℝ) ≤ t := by dsimp [t]; linarith
  have hbound : (t + D) ^ D + t + 9 ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (t + D) ^ D := by positivity
  have hpc : p ≤ (p + C) ^ C := by linarith
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr hpc)
  refine ⟨hdim, hdim, ?_⟩
  intro i j
  let π : CubicReplicatedIndex → Fin 2 := fun k =>
    if k.1 = 0 then a else if k.2.val = 0 then b else c
  let inp := fun x : Fin 2 → ℤ => cubicTrilinearInput (x a) (x b) (x c)
  have hinput (x : Fin 2 → ℤ) : (fun k => x (π k)) = inp x := by
    funext k
    rcases k with ⟨k, l⟩
    fin_cases k <;> fin_cases l <;> simp [π, inp, cubicTrilinearInput]
  let F (r : Fin 2 → ZMod 3) (x : Fin 2 → ℤ) :=
    V.eval i (inp x) * star (V.eval j (inp (fun k => x k - ((r k).val : ℤ))))
  have hF (r : Fin 2 → ZMod 3) :
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 t (F r)) := by
    obtain ⟨E⟩ := ((hshift V 0 (fun k => -((r (π k)).val : ℤ))).coordinatePullback π).expansion i j
    have hr (x : Fin 2 → ℤ) :
        (fun k => x (π k)) + (fun k => -((r (π k)).val : ℤ)) =
          inp (fun k => x k - ((r k).val : ℤ)) := by
      calc
        _ = (fun k => x (π k) - ((r (π k)).val : ℤ)) := by
          funext k
          simp only [Pi.add_apply, sub_eq_add_neg]
        _ = _ := hinput (fun k => x k - ((r k).val : ℤ))
    have heq : (fun x : Fin 2 → ℤ => V.eval i ((fun k => x (π k)) + 0) *
        star (V.eval j ((fun k => x (π k)) + (fun k => -((r (π k)).val : ℤ))))) = F r := by
      funext x
      rw [add_zero, hr, hinput]
    exact ⟨heq ▸ E.mono hat⟩
  have hterm (r : Fin 2 → ZMod 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2
      ((t + D) ^ D) (fun x => pairThirdIndicator r x * F r x)) :=
    hmul ht ((Classical.choice (hresidue r)).mono hbt) (Classical.choice (hF r))
  have hcoeff : (∑ _ : Fin 2 → ZMod 3, ‖(1 : ℂ)‖) ≤ Real.exp 9 := by
    simpa using card_pairThird_le_exp
  let S := NativeIntegerExpansion.weightedSum (fun r => Classical.choice (hterm r)) (fun _ => 1)
    (by norm_num : (0 : ℝ) ≤ 9) card_pairThird_le_exp hcoeff
  have hrep (x : Fin 2 → ℤ) :
      V.eval j (inp (fun k => x k - ((x k : ZMod 3).val : ℤ))) =
        W.eval j (inp (fun k => x k / 3)) := by
    have hminus : inp (fun k => x k - ((x k : ZMod 3).val : ℤ)) =
        (fun k => inp x k - ((inp x k : ZMod 3).val : ℤ)) := by
      funext k
      rcases k with ⟨k, l⟩
      fin_cases k <;> fin_cases l <;> rfl
    have hdiv : inp (fun k => x k / 3) = (fun k => inp x k / 3) := by
      funext k
      rcases k with ⟨k, l⟩
      fin_cases k <;> fin_cases l <;> rfl
    rw [hminus, hdiv]
    exact W.third_dilation_integer_representative (inp x) j
  have heq : (fun x => ∑ r : Fin 2 → ZMod 3, (1 : ℂ) * (pairThirdIndicator r x * F r x)) =
      (fun x => V.eval i (inp x) * star (W.eval j (inp (fun k => x k / 3)))) := by
    funext x
    let r : Fin 2 → ZMod 3 := fun k => (x k : ZMod 3)
    rw [Finset.sum_eq_single r]
    · simp only [pairThirdIndicator, r, ite_true, one_mul, F, hrep]
    · intro z _ hz
      have hne : (fun k => (x k : ZMod 3)) ≠ z := fun h => hz h.symm
      simp only [pairThirdIndicator, hne, ite_false, zero_mul, mul_zero]
    · simp
  rw [heq] at S
  exact ⟨S.mono (by linarith)⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_third_dilation_last_slots_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p),
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) = W.eval i x) →
      ∀ a b c : Fin 2, NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
        (fun j (x : Fin 2 → ℤ) =>
          (W.rationalDilation (1 / 3)).eval j (cubicTrilinearInput (x a) (x b) (x c)))
        (fun j x => (W.rationalDilation (1 / 3)).eval j (cubicTrilinearInput (x a) (x c) (x b))) := by
  obtain ⟨A, _, hcompare⟩ := exists_cubic_third_dilation_pattern_equivalence
  obtain ⟨B, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W hsymm a b c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hu : 0 ≤ (p + A) ^ A := by positivity
  have heq : (fun j (x : Fin 2 → ℤ) => W.eval j (cubicTrilinearInput (x a / 3) (x b / 3) (x c / 3))) =
      (fun j x => W.eval j (cubicTrilinearInput (x a / 3) (x c / 3) (x b / 3))) := by
    funext j x
    exact W.eval_cubicTrilinearInput_swap hsymm j _ _ _
  have F : NativeIntegerVectorEquivalence 2 ((p + A) ^ A)
      (fun j (x : Fin 2 → ℤ) => W.eval j (cubicTrilinearInput (x a / 3) (x b / 3) (x c / 3)))
      (fun j x => (W.rationalDilation (1 / 3)).eval j (cubicTrilinearInput (x a) (x c) (x b))) := by
    rw [heq]
    exact (hcompare W a c b).symm
  have H := htrans hu (hcompare W a b c) F (fun x => W.unit_eval _)
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact H.mono hcost

theorem exists_cubic_root_last_slots_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p),
      (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) i x,
        W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) = W.eval i x) →
      ∀ a b c : Fin 2, NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
        (fun j (x : Fin 2 → ℤ) => W.cubicRoot.eval j (cubicTrilinearInput (x a) (x b) (x c)))
        (fun j x => W.cubicRoot.eval j (cubicTrilinearInput (x a) (x c) (x b))) := by
  obtain ⟨A, _, hthird⟩ := exists_third_dilation_last_slots_equivalence
  obtain ⟨B, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_power_budget 9
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p W hsymm a b c
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hu : 0 ≤ (p + A) ^ A := by positivity
  have H := htensor hu (hthird W hsymm a b c)
  have hcost : ((p + A) ^ A + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have E := H.mono hcost
  have houtput : (W.rationalDilation (1 / 3)).outputDim = W.outputDim := rfl
  have hdim : (Fintype.card (Fin W.cubicRoot.outputDim) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    rw [Fintype.card_fin]
    change ((W.outputDim ^ 9 : ℕ) : ℝ) ≤ _
    simpa only [Fintype.card_fun, Fintype.card_fin, houtput] using E.left_dimension
  apply E.of_coordinate_maps _ _ (tensorIndexEquiv W.outputDim 9).symm
    (tensorIndexEquiv W.outputDim 9).symm _ _ hdim hdim (le_refl _)
  · intro j x
    rfl
  · intro j x
    rfl

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
