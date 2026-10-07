import OAI.Combinatorics.Progressions.Dynamics.GlobalErrorSplittingBudget
import OAI.Combinatorics.Progressions.Nilpotent.TotalDegreeNiltestSplitting

namespace OAI

section

namespace Erdos3.NativeTwoVariableSplit

open scoped TensorProduct BigOperators

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem exists_fixed_correlating_term {G X : Type*} [Fintype X] [Nonempty X]
    {s d : ℕ} {p epsilon rho : ℝ} {u : (Fin 2 → ℤ) → ℂ}
    (R : NativeTwoVariableSplit s d p epsilon u) (H : Finset G) (hH : H.Nonempty)
    (sample : G → X → Fin 2 → ℤ) (f : G → X → ℂ)
    (hrho : 0 < rho) (hepsilon : epsilon ≤ rho / 2)
    (hf : ∀ h ∈ H, ∀ x, ‖f h x‖ ≤ 1)
    (hcorr : ∀ h ∈ H, rho ≤ ‖𝔼 x, f h x * star (u (sample h x))‖) :
    ∃ (j : Fin R.count) (S : Finset G), S ⊆ H ∧ S.Nonempty ∧
      Real.exp (-p) * (H.card : ℝ) ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, rho / (2 * Real.exp p) ≤
        ‖𝔼 x, f h x * star ((R.test false j).eval (sample h x) *
          (R.test true j).eval (sample h x))‖ := by
  classical
  let rel (h : G) (_ : Unit) (j : Fin R.count) : Prop :=
    rho / (2 * Real.exp p) ≤
      ‖𝔼 x, f h x * star ((R.test false j).eval (sample h x) *
        (R.test true j).eval (sample h x))‖
  have hcount : (Fintype.card (Fin R.count) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using R.count_bound
  have hchoice : ∀ h ∈ H, ∀ i, ∃ j, rel h i j := by
    intro h hh _
    apply exists_correlating_summand (J := Fin R.count) Finset.univ_nonempty
      (f h) (fun x => u (sample h x))
      (fun j x => (R.test false j).eval (sample h x) * (R.test true j).eval (sample h x))
      hrho (Real.exp_pos p) hcount (fun x _ => hf h hh x) _ (hcorr h hh)
    intro x _
    rw [norm_sub_rev]
    exact (R.approximation (sample h x)).trans hepsilon
  obtain ⟨j, S, hsub, hS, hsize, hfixed⟩ :=
    exists_large_fixed_choices H hH rel hchoice hcount
  refine ⟨j (), S, hsub, hS, ?_, fun h hh => hfixed h hh ()⟩
  simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize

end Erdos3.NativeTwoVariableSplit

end

section

namespace Erdos3.NativeVectorEquivalence

open scoped TensorProduct BigOperators

attribute [local instance] NativeNilsequenceExpansion.lie NativeNilsequenceExpansion.algebra
  NativeNilsequenceExpansion.topology NativeNilsequenceExpansion.topologicalAdd
  NativeNilsequenceExpansion.continuousSMul NativeNilsequenceExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem transfer_correlation {I J K : Type*} [Fintype J] [Fintype K]
    {s N : ℕ} [NeZero N] {p : ℝ} {chi : J → ZMod N → ℂ} {chi' : K → ZMod N → ℂ}
    (E : NativeVectorEquivalence s N p chi chi')
    (hunit : ∀ x, ∑ k, ‖chi' k x‖ ^ 2 = 1) (f : I → ZMod N → ℂ)
    (W : NativeVectorCorrelation s N p
      (fun ij : I × J => fun x => f ij.1 x * star (chi ij.2 x))) :
    Nonempty (NativeVectorCorrelation s N (productNiltestBudget (3 * p + 4))
      (fun ik : I × K => fun x => f ik.1 x * star (chi' ik.2 x))) := by
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let R (k : K) := Classical.choice (E.expansion W.coordinate.2 k)
  let psi (k : K) (a : Fin (R k).count) (x : ZMod N) : ℂ :=
    star (((R k).test a).evalCyclic N (fun _ => x))
  have hExpansion (k : K) (x : ZMod N) (_hx : x ∈ (Finset.univ : Finset (ZMod N))) :
      star (chi W.coordinate.2 x) * star (star (chi' k x)) =
        ∑ a, star ((R k).coefficient a) * psi k a x := by
    have h := congrArg star ((R k).eval x)
    simpa only [psi, star_sum, star_mul, star_star, mul_comm] using h
  have hCorr : Real.exp (-p) ≤
      ‖𝔼 x ∈ (Finset.univ : Finset (ZMod N)),
        (f W.coordinate.1 x * star (W.test.evalCyclic N (fun _ => x))) *
          star (chi W.coordinate.2 x)‖ := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using W.correlation
  obtain ⟨k, a, hka⟩ := exists_unit_expansion_correlation Finset.univ
    (fun x => f W.coordinate.1 x * star (W.test.evalCyclic N (fun _ => x)))
    (fun x => star (chi W.coordinate.2 x)) (fun k x => star (chi' k x))
    (fun k a => star ((R k).coefficient a)) psi
    (fun x _ => by simpa only [norm_star] using hunit x) hExpansion
    (Real.exp_pos (-p)) (Real.exp_pos p) (Real.exp_pos p) E.right_dimension
    (fun k => by simpa only [norm_star] using (R k).cost) hCorr
  have hfrac : Real.exp (-p) / (Real.exp p * Real.exp p) = Real.exp (-(3 * p)) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [hfrac] at hka
  have hpq : p ≤ 3 * p + 4 := by linarith
  let g (ik : I × K) (x : ZMod N) := f ik.1 x * star (chi' ik.2 x)
  let T := (R k).test a
  have hW : NativeVectorCorrelation s N (3 * p + 4)
      (fun iu : (I × K) × Unit => fun x => g iu.1 x * star (T.evalCyclic N (fun _ => x))) := {
    L := W.L
    dim := W.dim
    model := W.model
    test := W.test
    complexity := W.complexity.mono hpq
    coordinate := ((W.coordinate.1, k), ())
    correlation := by
      have h := (Real.exp_le_exp.mpr (show -(3 * p + 4) ≤ -(3 * p) by linarith)).trans hka
      simpa only [g, T, psi, mul_assoc, mul_left_comm, mul_comm] using h
  }
  exact NativeVectorCorrelation.exists_absorb ((R k).model a) (fun _ : Unit => T) g
    (by linarith : 2 ≤ 3 * p + 4) (fun _ => ((R k).complexity a).mono hpq) hW

end Erdos3.NativeVectorEquivalence

end

section

namespace Erdos3.NativeNilsequenceExpansion

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem absorb_correlation {I : Type*} {s N : ℕ} [NeZero N] {p : ℝ}
    {eta : ZMod N → ℂ} (E : NativeNilsequenceExpansion s N p eta)
    (f : I → ZMod N → ℂ)
    (W : NativeVectorCorrelation s N p (fun i x => f i x * star (eta x))) :
    Nonempty (NativeVectorCorrelation s N (productNiltestBudget (3 * p + 4)) f) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hdim : (Fintype.card Unit : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_unit, Nat.cast_one] using Real.one_le_exp hp
  let V : NativeVectorEquivalence s N p (fun _ : Unit => eta) (fun _ : Unit => fun _ => 1) := {
    left_dimension := hdim
    right_dimension := hdim
    expansion := fun _ _ => by
      simpa only [star_one, mul_one] using (show Nonempty (NativeNilsequenceExpansion s N p eta) from ⟨E⟩) }
  let W' : NativeVectorCorrelation s N p
      (fun iu : I × Unit => fun x => f iu.1 x * star (eta x)) :=
    { W with coordinate := (W.coordinate, ()) }
  obtain ⟨R⟩ := V.transfer_correlation (fun _ => by simp) f W'
  exact ⟨{ R with
    coordinate := R.coordinate.1
    correlation := by simpa only [star_one, mul_one] using R.correlation }⟩

end Erdos3.NativeNilsequenceExpansion

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

noncomputable def normalizedErrorCorrelator (b : ℝ) (m : ZMod N → ZMod N → ℂ)
    (h x : ZMod N) : ℂ :=
  multiplicativeDerivative f h x * star (m h x * W.normalizedLower b h x)

theorem normalizedErrorCorrelator_norm {b : ℝ} (hpb : p ≤ b)
    (hf : ∀ x, ‖f x‖ ≤ 1) (m : ZMod N → ZMod N → ℂ) (hm : ∀ h x, ‖m h x‖ ≤ 1)
    (h x : ZMod N) : ‖W.normalizedErrorCorrelator b m h x‖ ≤ 1 := by
  simp only [normalizedErrorCorrelator, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (by positivity)
    (multiplicativeDerivative_norm_le_one f hf h x)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (hm h x)).trans
        (W.normalizedLower_norm hpb h x))

theorem normalizedErrorCorrelator_correlation {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} {D : RationalFilteredNilmanifold L s d}
    (T : D.Niltest (fun _ : Fin 2 => 1)) (b : ℝ) (m : ZMod N → ZMod N → ℂ)
    (h : ZMod N) (hh : h ∈ W.shifts)
    (hcorr : Real.exp (-b) ≤ ‖𝔼 x, multiplicativeDerivative f h x * star
      (m h x * (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
        T.eval ![(h.val : ℤ), (x.val : ℤ)])‖) :
    Real.exp (-(3 * b)) ≤ ‖𝔼 x, W.normalizedErrorCorrelator b m h x *
      star ((T.expNormalize b).eval ![(h.val : ℤ), (x.val : ℤ)])‖ := by
  have hc : (Real.exp (-(2 * b)) : ℂ) = (Real.exp (-b) : ℂ) * (Real.exp (-b) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring_nf
  have hmean : (𝔼 x, W.normalizedErrorCorrelator b m h x *
        star ((T.expNormalize b).eval ![(h.val : ℤ), (x.val : ℤ)])) =
      (Real.exp (-(2 * b)) : ℂ) * (𝔼 x, multiplicativeDerivative f h x * star
        (m h x * (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
          T.eval ![(h.val : ℤ), (x.val : ℤ)])) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    rw [normalizedErrorCorrelator, W.normalizedLower_of_mem b h hh]
    simp only [RationalFilteredNilmanifold.Niltest.expNormalize,
      RationalFilteredNilmanifold.Niltest.scaleComplex_eval,
      RationalFilteredNilmanifold.Niltest.scaleComplex_evalCyclic, hc,
      star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    _ = Real.exp (-(2 * b)) * Real.exp (-b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

def GlobalErrorSplittingStatement (s C : ℕ) : Prop :=
    ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f)
      {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d}
      (T : D.Niltest (fun _ : Fin 2 => 1)) (b : ℝ),
      2 ≤ b → p ≤ b → T.ComplexityLE b →
      ∀ (H : Finset (ZMod N)) (hsub : H ⊆ W.shifts), H.Nonempty →
      ∀ m : ZMod N → ZMod N → ℂ, (∀ h x, ‖m h x‖ ≤ 1) → (∀ x, ‖f x‖ ≤ 1) →
      (∀ h (hh : h ∈ H), Real.exp (-b) ≤
        ‖𝔼 x, multiplicativeDerivative f h x * star
          (m h x * (W.selectedWitness ⟨h, hsub hh⟩).test.evalCyclic N (fun _ => x) *
            T.eval ![(h.val : ℤ), (x.val : ℤ)])‖) →
      ∃ (weight : ZMod N → ℂ) (S : Finset (ZMod N)),
        (∀ x, ‖weight x‖ ≤ 1) ∧ S ⊆ H ∧ S.Nonempty ∧
        Real.exp (-((b + C) ^ C)) * (H.card : ℝ) ≤ (S.card : ℝ) ∧
        ∀ h ∈ S, Nonempty (NativeVectorCorrelation (s - 1) N ((b + C) ^ C)
          (fun _ : Unit => fun x => multiplicativeDerivative f h x * star (m h x * weight x)))

end Erdos3

end

section

namespace Erdos3.NativeCorrelationStructure

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff
  NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem absorb_split_term {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (W : NativeCorrelationStructure s r N p f)
    {d : ℕ} {B epsilon : ℝ} {u : (Fin 2 → ℤ) → ℂ}
    (R : NativeTwoVariableSplit s d B epsilon u) (j : Fin R.count)
    (m : ZMod N → ZMod N → ℂ) (weight : ZMod N → ℂ)
    (h : ZMod N) (hmem : h ∈ W.shifts) {b F Q : ℝ}
    (hpb : p ≤ b) (hbQ : b ≤ Q) (hFQ : F ≤ Q)
    (E : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) F
      (fun x => (R.test true j).eval ![(h.val : ℤ), x ()]))
    (hfirst : ∀ x : ZMod N, (R.test false j).eval ![(h.val : ℤ), (x.val : ℤ)] = weight x)
    (hcorr : Real.exp (-Q) ≤
      ‖𝔼 x, W.normalizedErrorCorrelator b m h x * star
        ((R.test false j).eval ![(h.val : ℤ), (x.val : ℤ)] *
          (R.test true j).eval ![(h.val : ℤ), (x.val : ℤ)])‖) :
    Nonempty (NativeVectorCorrelation (s - 1) N (productNiltestBudget (3 * Q + 4))
      (fun _ : Unit => fun x => multiplicativeDerivative f h x * star (m h x * weight x))) := by
  let U := (W.selectedWitness ⟨h, hmem⟩).test.expNormalize b
  have hU : U.ComplexityLE b :=
    (W.selectedWitness ⟨h, hmem⟩).test.expNormalize_complexity
      ((W.selectedWitness ⟨h, hmem⟩).complexity.mono hpb)
  let g (_ : Unit) (x : ZMod N) := multiplicativeDerivative f h x * star (m h x * weight x)
  let Z : NativeVectorCorrelation (s - 1) N Q
      (fun z : Unit => fun x => g z x * star ((R.test true j).eval ![(h.val : ℤ), (x.val : ℤ)])) := {
    L := (W.selectedWitness ⟨h, hmem⟩).L
    dim := (W.selectedWitness ⟨h, hmem⟩).dim
    model := (W.selectedWitness ⟨h, hmem⟩).model
    test := U
    complexity := hU.mono hbQ
    coordinate := ()
    correlation := by
      simpa only [g, normalizedErrorCorrelator,
        W.normalizedLower_of_mem b h hmem, hfirst, U, star_mul,
        mul_assoc, mul_left_comm, mul_comm] using hcorr }
  exact ((E.toCyclic N).mono hFQ).absorb_correlation g Z

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff
  NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem exists_split_global_error (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ GlobalErrorSplittingStatement s C := by
  obtain ⟨a, _, hsplit⟩ := exists_totalDegree_niltest_splitting s 2
  obtain ⟨c, _, hfreeze⟩ := NativeTwoVariableSplit.exists_second_expansion_budget s
  obtain ⟨C, hC, hbudget⟩ := exists_global_error_budget a c
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W L _ _ _ _ _ _ d D T b hb hpb hT H hsub hH m hm hf hcorr
  have hb0 : 0 ≤ b := by linarith only [hb]
  let B := (b + a) ^ a
  let F := (B + c) ^ c
  let Q := 3 * b + B + F + 3
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hbQ : b ≤ Q := by dsimp [Q]; linarith only [hb0, hB, hF]
  have hFQ : F ≤ Q := by dsimp [Q]; linarith only [hb0, hB]
  have hcQ : 3 * b + B + 1 ≤ Q := by dsimp [Q]; linarith only [hF]
  have hcostB : B ≤ (b + C) ^ C := (hbudget b hb0).1
  have hcost : productNiltestBudget (3 * Q + 4) ≤ (b + C) ^ C := (hbudget b hb0).2
  let epsilon := Real.exp (-(3 * b + 1))
  have hscale : 1 / epsilon ≤ Real.exp ((b + 2) ^ 2) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith only [hb0, sq_nonneg b]
  have hR : Nonempty (NativeTwoVariableSplit s d B epsilon (T.expNormalize b).eval) :=
    hsplit (T.expNormalize b) (T.expNormalize_complexity hT)
      (T.expNormalize_norm hT) epsilon (Real.exp_pos _) hscale
  obtain ⟨R⟩ := hR
  have hepsilon : epsilon ≤ Real.exp (-(3 * b)) / 2 := by
    simpa only [epsilon, show -(3 * b + 1) = -(3 * b) - 1 by ring] using
      exp_sub_one_le_half_exp (-(3 * b))
  obtain ⟨j, S, hSH, hS, hsize, hterm⟩ := R.exists_fixed_correlating_term H hH
    (fun (h x : ZMod N) => ![(h.val : ℤ), (x.val : ℤ)]) (W.normalizedErrorCorrelator b m)
    (Real.exp_pos _) hepsilon
    (fun h _ x => W.normalizedErrorCorrelator_norm hpb hf m hm h x)
    (fun h hh => W.normalizedErrorCorrelator_correlation T b m h (hsub hh) (hcorr h hh))
  let weight (x : ZMod N) := (R.test false j).eval ![0, (x.val : ℤ)]
  have hweight (x : ZMod N) : ‖weight x‖ ≤ 1 :=
    ((R.test false j).norm_eval_le _).trans
      (show ((R.test false j).normBound : ℝ) ≤ 1 from R.test_norm false j)
  have hfirst (h x : ZMod N) :
      (R.test false j).eval ![(h.val : ℤ), (x.val : ℤ)] = weight x :=
    R.first_eval_eq j _ _ rfl
  have hsmall : Real.exp (-(3 * b + B + 1)) ≤ Real.exp (-(3 * b)) / (2 * Real.exp B) := by
    calc
      _ = Real.exp (-(3 * b + B) - 1) := by congr 1; ring
      _ ≤ Real.exp (-(3 * b + B)) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by rw [show -(3 * b + B) = -(3 * b) - B by ring, Real.exp_sub]; ring
  refine ⟨weight, S, hweight, hSH, hS, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcostB))
      (Nat.cast_nonneg H.card)).trans hsize
  · intro h hh
    let hmem : h ∈ W.shifts := hsub (hSH hh)
    have hE : ∃ E : NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) F
        (fun x => (R.test true j).eval ![(h.val : ℤ), x ()]), E.count = 1 :=
      hfreeze R j (h.val : ℤ)
    obtain ⟨E, _⟩ := hE
    have hz := (Real.exp_le_exp.mpr (neg_le_neg hcQ)).trans (hsmall.trans (hterm h hh))
    obtain ⟨V⟩ := W.absorb_split_term R j m weight h hmem hpb hbQ hFQ E (hfirst h) hz
    exact ⟨V.mono hcost⟩

end Erdos3

end

end OAI
