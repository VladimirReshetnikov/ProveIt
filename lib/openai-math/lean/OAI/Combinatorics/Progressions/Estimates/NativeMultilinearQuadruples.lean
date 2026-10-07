import OAI.Combinatorics.Progressions.Estimates.CubicAntisymmetricTransfer

namespace OAI

section

namespace Erdos3.NativeCorrelationStructure

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

variable {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
  (W : NativeCorrelationStructure s r N p f)

theorem exists_fixed_transferred_correlation {K : Type*} [Fintype K] {q : ℝ}
    {eta : K → (Fin 2 → ℤ) → ℂ}
    (E : NativeIntegerVectorEquivalence s q W.mixed.eval eta)
    (hunit : ∀ x, ∑ k, ‖eta k x‖ ^ 2 = 1) :
    ∃ (j : Fin W.mixed.outputDim) (k : K)
      (a : Fin (E.selectedExpansion j k).count) (i : Fin W.family.outputDim)
      (H : Finset (ZMod N)), H ⊆ W.shifts ∧ H.Nonempty ∧
      Real.exp (-(3 * p + 2 * q)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, ∃ hh : h ∈ W.shifts,
        (W.selectedWitness ⟨h, hh⟩).coordinate = (j, i) ∧
        Real.exp (-(p + 2 * q)) ≤
          ‖𝔼 x, multiplicativeDerivative f h x * star
            (eta k (correlationInput (h.val : ℤ) (x.val : ℤ)) *
              W.family.evalCyclic N i h x *
              (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
              ((E.selectedExpansion j k).test a).eval
                (correlationInput (h.val : ℤ) (x.val : ℤ)))‖ := by
  classical
  let P := E.ExpansionIndex × Fin W.family.outputDim
  let rel (h : ZMod N) (_ : Unit) (c : P) : Prop :=
    ∃ hh : h ∈ W.shifts,
      (W.selectedWitness ⟨h, hh⟩).coordinate = (c.1.1, c.2) ∧
      Real.exp (-(p + 2 * q)) ≤
        ‖𝔼 x, multiplicativeDerivative f h x * star
          (eta c.1.2.1 (correlationInput (h.val : ℤ) (x.val : ℤ)) *
            W.family.evalCyclic N c.2 h x *
            (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
            ((E.selectedExpansion c.1.1 c.1.2.1).test c.1.2.2).eval
              (correlationInput (h.val : ℤ) (x.val : ℤ)))‖
  have hchoice : ∀ h ∈ W.shifts, ∀ u, ∃ c, rel h u c := by
    intro h hh _
    obtain ⟨k, a, hcorr⟩ := W.mixed_correlation_transfer E hunit ⟨h, hh⟩
    refine ⟨(⟨(W.selectedWitness ⟨h, hh⟩).coordinate.1, k, a⟩,
      (W.selectedWitness ⟨h, hh⟩).coordinate.2), hh, ?_, hcorr⟩
    exact (Prod.eta _).symm
  have hcount : (Fintype.card P : ℝ) ≤ Real.exp (2 * p + 2 * q) := by
    have hleft : (Fintype.card (Fin W.mixed.outputDim) : ℝ) ≤ Real.exp p := by
      simpa only [Fintype.card_fin] using W.mixed.output_bound
    have hindex := E.expansionIndex_card_bound hleft E.right_dimension
    change (Fintype.card (E.ExpansionIndex × Fin W.family.outputDim) : ℝ) ≤ _
    rw [Fintype.card_prod, Nat.cast_mul, Fintype.card_fin]
    calc
      _ ≤ Real.exp (p + q + q) * Real.exp p :=
        mul_le_mul hindex W.family.output_bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨c, H, hsub, hH, hsize, hfixed⟩ :=
    exists_large_fixed_choices W.shifts W.nonempty rel hchoice hcount
  have hsize' : Real.exp (-(2 * p + 2 * q)) * (W.shifts.card : ℝ) ≤ (H.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hsize
  refine ⟨(c ()).1.1, (c ()).1.2.1, (c ()).1.2.2, (c ()).2, H, hsub, hH,
    ?_, fun h hh => hfixed h hh ()⟩
  calc
    _ = Real.exp (-(2 * p + 2 * q)) *
        (Real.exp (-p) * Fintype.card (ZMod N)) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-(2 * p + 2 * q)) * (W.shifts.card : ℝ) :=
      mul_le_mul_of_nonneg_left W.density (Real.exp_nonneg _)
    _ ≤ _ := hsize'

end Erdos3.NativeCorrelationStructure

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_fixed_multilinearized_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f),
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ E : NativeIntegerVectorEquivalence s ((p + C) ^ C)
            W.mixed.eval (fun k x => V.eval k (fun j => x j.1)),
          ∃ (j : Fin W.mixed.outputDim) (k : Fin V.outputDim)
            (a : Fin (E.selectedExpansion j k).count) (i : Fin W.family.outputDim)
            (H : Finset (ZMod N)), H ⊆ W.shifts ∧ H.Nonempty ∧
            Real.exp (-(3 * p + 2 * (p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
            ∀ h ∈ H, ∃ hh : h ∈ W.shifts,
              (W.selectedWitness ⟨h, hh⟩).coordinate = (j, i) ∧
              Real.exp (-(p + 2 * (p + C) ^ C)) ≤
                ‖𝔼 x, multiplicativeDerivative f h x * star
                  (V.eval k (fun l => correlationInput (h.val : ℤ) (x.val : ℤ) l.1) *
                    W.family.evalCyclic N i h x *
                    (W.selectedWitness ⟨h, hh⟩).test.evalCyclic N (fun _ => x) *
                    ((E.selectedExpansion j k).test a).eval
                      (correlationInput (h.val : ℤ) (x.val : ℤ)))‖ := by
  obtain ⟨C, hC, htransfer⟩ := exists_multilinearized_correlation s
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W
  obtain ⟨V, hdim, hsymm, E, _⟩ := htransfer W
  exact ⟨V, hdim, hsymm, E, W.exists_fixed_transferred_correlation E
    (fun x => V.unit_eval (fun j => x j.1))⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_weighted_multilinear_correlation_with_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C) W.mixed.eval
          (fun k x => V.eval k (fun j => x j.1)) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
            (fun _ : Unit => fun x => multiplicativeDerivative f h x * star
              ((V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
                W.family.evalCyclic N i h x) * weight x))) := by
  obtain ⟨a, _, hmulti⟩ := exists_fixed_multilinearized_correlation s
  obtain ⟨c, _, hsplit⟩ := exists_split_global_error s
  let X : Polynomial ℕ := Polynomial.X
  let Q₀ := (X + Polynomial.C a) ^ a
  let B₀ := 2 * X + 3 * Q₀ + 3
  let R₀ := (B₀ + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * X + 4 * Q₀ + R₀ + 4)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  let b := 2 * p + 3 * q + 3
  let R := (b + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 2 ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hpb : p ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hqb : q ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hcb : p + 2 * q ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpoly : 4 * p + 4 * q + R + 4 ≤ (p + C) ^ C := by
    simpa [X, Q₀, B₀, R₀, q, b, R, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  have hRC : R ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  have hdenseC : 3 * p + 2 * q + R ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  obtain ⟨V, hdim, hsymm, E, j, k, z, i, H, hsub, hH, hdense, hcorr⟩ := hmulti W
  let T := (E.selectedExpansion j k).test z
  let m (h x : ZMod N) :=
    V.eval k (fun l => correlationInput (h.val : ℤ) (x.val : ℤ) l.1) *
      W.family.evalCyclic N i h x
  have hm (h x : ZMod N) : ‖m h x‖ ≤ 1 := by
    dsimp only [m]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hinput (h n : ℤ) : correlationInput h n = ![h, n] := by
    funext t
    fin_cases t <;> rfl
  have hcor' (h : ZMod N) (hh : h ∈ H) : Real.exp (-b) ≤
      ‖𝔼 x, multiplicativeDerivative f h x * star
        (m h x * (W.selectedWitness ⟨h, hsub hh⟩).test.evalCyclic N (fun _ => x) *
          T.eval ![(h.val : ℤ), (x.val : ℤ)])‖ := by
    obtain ⟨hh', _, hc⟩ := hcorr h hh
    apply (Real.exp_le_exp.mpr (neg_le_neg hcb)).trans
    simpa only [m, T, hinput] using hc
  obtain ⟨weight, S, hweight, hSH, hS, hsize, hnew⟩ := hsplit W T b hb hpb
    (((E.selectedExpansion j k).complexity z).mono hqb) H hsub hH m hm hf hcor'
  have htotal : Real.exp (-(3 * p + 2 * q + R)) * Fintype.card (ZMod N) ≤ (S.card : ℝ) := by
    calc
      _ = Real.exp (-R) * (Real.exp (-(3 * p + 2 * q)) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-R) * (H.card : ℝ) := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  refine ⟨V.mono hqC, hdim, hsymm, E.mono hqC, k, i, weight, S, hweight, hSH.trans hsub, hS, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hdenseC))
      (Nat.cast_nonneg _)).trans htotal
  · intro h hh
    obtain ⟨Z⟩ := hnew h hh
    exact ⟨Z.mono hRC⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_weighted_multilinear_correlation (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
            (fun _ : Unit => fun x => multiplicativeDerivative f h x * star
              ((V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
                W.family.evalCyclic N i h x) * weight x))) := by
  obtain ⟨a, _, hmulti⟩ := exists_fixed_multilinearized_correlation s
  obtain ⟨c, _, hsplit⟩ := exists_split_global_error s
  let X : Polynomial ℕ := Polynomial.X
  let Q₀ := (X + Polynomial.C a) ^ a
  let B₀ := 2 * X + 3 * Q₀ + 3
  let R₀ := (B₀ + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * X + 4 * Q₀ + R₀ + 4)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  let b := 2 * p + 3 * q + 3
  let R := (b + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hb : 2 ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hpb : p ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hqb : q ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hcb : p + 2 * q ≤ b := by dsimp [b]; linarith only [hp, hq]
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpoly : 4 * p + 4 * q + R + 4 ≤ (p + C) ^ C := by
    simpa [X, Q₀, B₀, R₀, q, b, R, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  have hRC : R ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  have hdenseC : 3 * p + 2 * q + R ≤ (p + C) ^ C := by linarith only [hp, hq, hR, hpoly]
  obtain ⟨V, hdim, hsymm, E, j, k, z, i, H, hsub, hH, hdense, hcorr⟩ := hmulti W
  let T := (E.selectedExpansion j k).test z
  let m (h x : ZMod N) :=
    V.eval k (fun l => correlationInput (h.val : ℤ) (x.val : ℤ) l.1) *
      W.family.evalCyclic N i h x
  have hm (h x : ZMod N) : ‖m h x‖ ≤ 1 := by
    dsimp only [m]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hinput (h n : ℤ) : correlationInput h n = ![h, n] := by
    funext t
    fin_cases t <;> rfl
  have hcor' (h : ZMod N) (hh : h ∈ H) : Real.exp (-b) ≤
      ‖𝔼 x, multiplicativeDerivative f h x * star
        (m h x * (W.selectedWitness ⟨h, hsub hh⟩).test.evalCyclic N (fun _ => x) *
          T.eval ![(h.val : ℤ), (x.val : ℤ)])‖ := by
    obtain ⟨hh', _, hc⟩ := hcorr h hh
    apply (Real.exp_le_exp.mpr (neg_le_neg hcb)).trans
    simpa only [m, T, hinput] using hc
  obtain ⟨weight, S, hweight, hSH, hS, hsize, hnew⟩ := hsplit W T b hb hpb
    (((E.selectedExpansion j k).complexity z).mono hqb) H hsub hH m hm hf hcor'
  have htotal : Real.exp (-(3 * p + 2 * q + R)) * Fintype.card (ZMod N) ≤ (S.card : ℝ) := by
    calc
      _ = Real.exp (-R) * (Real.exp (-(3 * p + 2 * q)) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-R) * (H.card : ℝ) := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  refine ⟨V.mono hqC, hdim, hsymm, k, i, weight, S, hweight, hSH.trans hsub, hS, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hdenseC))
      (Nat.cast_nonneg _)).trans htotal
  · intro h hh
    obtain ⟨Z⟩ := hnew h hh
    exact ⟨Z.mono hRC⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_multilinear_quadruples_with_equivalence (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C) W.mixed.eval
          (fun k x => V.eval k (fun j => x j.1)) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∃ U : NativeCrossWitnesses (s - 1) N ((p + C) ^ C)
              (fun x => f x * star (weight x)) f
              (fun h x => V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
                W.family.evalCyclic N i h x) H,
            ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
                Real.exp (-((p + C) ^ C)) ≤
                  additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  obtain ⟨a, _, hweighted⟩ := exists_weighted_multilinear_correlation_with_equivalence s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (13 * (X + Polynomial.C a) ^ a + 2)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hQbudget : 13 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hQbudget]
  obtain ⟨V, hdim, hsymm, E, k, i, weight, H, hweight, hsub, hH, hdense, hcorr⟩ := hweighted W hf
  let f₀ (x : ZMod N) := f x * star (weight x)
  let m (h x : ZMod N) := V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
    W.family.evalCyclic N i h x
  have hf₀ (x : ZMod N) : ‖f₀ x‖ ≤ 1 := by
    simp only [f₀, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x)).trans (hweight x)
  have hm (h x : ZMod N) : ‖m h x‖ ≤ 1 := by
    simp only [m, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hc (h : H) : Nonempty (NativeVectorCorrelation (s - 1) N q (nativeCrossResidual f₀ f m h.val)) := by
    obtain ⟨R⟩ := hcorr h.val h.property
    refine ⟨{ R with correlation := ?_ }⟩
    simpa only [nativeCrossResidual, f₀, m, multiplicativeDerivative, star_mul,
      mul_assoc, mul_left_comm, mul_comm] using R.correlation
  let U : NativeCrossWitnesses (s - 1) N q f₀ f m H := fun h => Classical.choice (hc h)
  obtain ⟨Q, hQ, hsize, hquad⟩ := U.exists_quadruples_budget hH hf₀ hf hm hdense
  refine ⟨V.mono hqC, hdim, hsymm, E.mono hqC, k, i, weight, H, hweight, hsub, hH, ?_, U.mono hqC,
    Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hQbudget))
      (by positivity)).trans hsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hcor⟩ := hquad t ht
    refine ⟨h₁, h₂, h₃, h₄, ?_⟩
    change Real.exp (-((p + C) ^ C)) ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2
    exact (Real.exp_le_exp.mpr (neg_le_neg hQbudget)).trans hcor

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_multilinear_quadruples (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      ∃ V : NativeMultidegreeNilcharacter
          (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) ((p + C) ^ C),
        V.dim ≤ 2 ^ (s + 1) * W.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree s)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree s) e).symm j)) =
            V.eval k x) ∧
        ∃ (k : Fin V.outputDim) (i : Fin W.family.outputDim) (weight : ZMod N → ℂ)
          (H : Finset (ZMod N)), (∀ x, ‖weight x‖ ≤ 1) ∧ H ⊆ W.shifts ∧ H.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
          ∃ U : NativeCrossWitnesses (s - 1) N ((p + C) ^ C)
              (fun x => f x * star (weight x)) f
              (fun h x => V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
                W.family.evalCyclic N i h x) H,
            ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
                Real.exp (-((p + C) ^ C)) ≤
                  additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2 := by
  obtain ⟨a, _, hweighted⟩ := exists_weighted_multilinear_correlation s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (13 * (X + Polynomial.C a) ^ a + 2)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.mixed.dim).trans W.mixed.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hQbudget : 13 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hQbudget]
  obtain ⟨V, hdim, hsymm, k, i, weight, H, hweight, hsub, hH, hdense, hcorr⟩ := hweighted W hf
  let f₀ (x : ZMod N) := f x * star (weight x)
  let m (h x : ZMod N) := V.eval k (fun j => correlationInput (h.val : ℤ) (x.val : ℤ) j.1) *
    W.family.evalCyclic N i h x
  have hf₀ (x : ZMod N) : ‖f₀ x‖ ≤ 1 := by
    simp only [f₀, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf x)).trans (hweight x)
  have hm (h x : ZMod N) : ‖m h x‖ ≤ 1 := by
    simp only [m, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval k _)).trans
      (W.family.norm_eval i h (x.val : ℤ))
  have hc (h : H) : Nonempty (NativeVectorCorrelation (s - 1) N q (nativeCrossResidual f₀ f m h.val)) := by
    obtain ⟨R⟩ := hcorr h.val h.property
    refine ⟨{ R with correlation := ?_ }⟩
    simpa only [nativeCrossResidual, f₀, m, multiplicativeDerivative, star_mul,
      mul_assoc, mul_left_comm, mul_comm] using R.correlation
  let U : NativeCrossWitnesses (s - 1) N q f₀ f m H := fun h => Classical.choice (hc h)
  obtain ⟨Q, hQ, hsize, hquad⟩ := U.exists_quadruples_budget hH hf₀ hf hm hdense
  refine ⟨V.mono hqC, hdim, hsymm, k, i, weight, H, hweight, hsub, hH, ?_, U.mono hqC,
    Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hQbudget))
      (by positivity)).trans hsize
  · intro t ht
    obtain ⟨h₁, h₂, h₃, h₄, hcor⟩ := hquad t ht
    refine ⟨h₁, h₂, h₃, h₄, ?_⟩
    change Real.exp (-((p + C) ^ C)) ≤ additiveQuadrupleCorrelation U.extension t.1 t.2.1 t.2.2
    exact (Real.exp_le_exp.mpr (neg_le_neg hQbudget)).trans hcor

end Erdos3

end

end OAI
