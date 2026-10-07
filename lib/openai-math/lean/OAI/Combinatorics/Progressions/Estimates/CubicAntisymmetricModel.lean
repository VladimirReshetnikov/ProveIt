import OAI.Combinatorics.Progressions.Estimates.NativeRetainedTargetCubeIntervals
import OAI.Combinatorics.Progressions.Lattices.IntegerIntervalCyclicAverage
import OAI.Combinatorics.Progressions.Polynomial.DenseRowPhaseAlignment

namespace OAI

section

namespace Erdos3

theorem cyclicBranchOffset_zmod {N : ℕ} [NeZero N] (h : ZMod N) (branch : Bool) :
    ((cyclicBranchOffset h branch : ℤ) : ZMod N) = h := by
  cases branch <;> simp [cyclicBranchOffset]

theorem exists_cubic_diagonal_weights {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (A B : ℤ → ℤ → ℂ) (hA : ∀ h n, ‖A h n‖ ≤ 1) (hB : ∀ n k, ‖B n k‖ ≤ 1) :
    ∃ A' B' : ℤ → ℤ → ℂ, (∀ h n, ‖A' h n‖ ≤ 1) ∧ (∀ n k, ‖B' n k‖ ≤ 1) ∧
      ∀ h n k : ℤ, ∀ z : ℂ,
        (multiplicativeDerivative (multiplicativeDerivative f (k : ZMod N)) (h : ZMod N)
          (n : ZMod N) * z) * A h n * B n k =
        f ((n + h + k : ℤ) : ZMod N) * z * A' h n * B' n k := by
  let A' (h n : ℤ) := (A h n * f (n : ZMod N)) * star (f ((n + h : ℤ) : ZMod N))
  let B' (n k : ℤ) := B n k * star (f ((n + k : ℤ) : ZMod N))
  refine ⟨A', B', ?_, ?_, ?_⟩
  · intro h n
    simp only [A', norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((mul_le_of_le_one_left (norm_nonneg _) (hA h n)).trans (hf _))).trans (hf _)
  · intro n k
    simp only [B', norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hB n k)).trans (hf _)
  · intro h n k z
    simp only [A', B', multiplicativeDerivative, star_mul, star_star, Int.cast_add]
    ring

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_absorb_cubic_error :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L 2 d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin 3 => 1)), T.ComplexityLE p →
      ∀ {G : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset ℤ), (∀ t ∈ H, (S t).Nonempty) →
      ∀ (h k : G → ℤ) (f : G → ℤ → ℂ),
      (∀ t ∈ H, ∀ n ∈ S t, ‖f t n‖ ≤ 1) →
      (∀ t ∈ H, Real.exp (-p) ≤ ‖𝔼 n ∈ S t, f t n * star (T.eval ![h t, n, k t])‖) →
      ∃ A B : ℤ → ℤ → ℂ, (∀ h n, ‖A h n‖ ≤ 1) ∧ (∀ n k, ‖B n k‖ ≤ 1) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ t ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 n ∈ S t, f t n * A (h t) n * B n (k t)‖ := by
  obtain ⟨C, hC, habsorb⟩ := exists_absorb_missing_coordinate_error 2
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT G H hH S hS h k f hf hcorr
  obtain ⟨F, hF, hdep, H', hsub, hH', hdense, hfixed⟩ :=
    habsorb T hT H hH S hS (fun t n => ![h t, n, k t]) f hf hcorr
  let A (h n : ℤ) := F 2 ![h, n, 0]
  let B (n k : ℤ) := F 0 ![0, n, k]
  have hzero (h n k : ℤ) : F 0 ![h, n, k] = F 0 ![0, n, k] := by
    apply hdep
    intro i hi
    fin_cases i
    · exact (hi rfl).elim
    · rfl
    · rfl
  have hone (h n k : ℤ) : F 1 ![h, n, k] = F 1 ![h, 0, k] := by
    apply hdep
    intro i hi
    fin_cases i
    · rfl
    · exact (hi rfl).elim
    · rfl
  have htwo (h n k : ℤ) : F 2 ![h, n, k] = F 2 ![h, n, 0] := by
    apply hdep
    intro i hi
    fin_cases i
    · rfl
    · rfl
    · exact (hi rfl).elim
  refine ⟨A, B, (fun h n => hF 2 _), (fun n k => hF 0 _), H', hsub, hH', hdense, ?_⟩
  intro t ht
  have heq : (𝔼 n ∈ S t, f t n * ∏ i, F i ![h t, n, k t]) =
      (𝔼 n ∈ S t, f t n * A (h t) n * B n (k t)) * F 1 ![h t, 0, k t] := by
    rw [Finset.expect_mul]
    apply Finset.expect_congr rfl
    intro n _
    rw [Fin.prod_univ_three, hzero, hone, htwo]
    dsimp only [A, B]
    ring
  have hc := hfixed t ht
  rw [heq, norm_mul] at hc
  exact hc.trans ((mul_le_mul_of_nonneg_left (hF 1 _) (norm_nonneg _)).trans_eq (mul_one _))

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_cubic_trilinear_derivative_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) p),
      ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
        V.dim ≤ 8 * W.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
          V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) = V.eval k x) ∧
        NativeIntegerVectorEquivalence 2 ((p + C) ^ C) W.eval (fun k x => V.eval k (fun j => x j.1)) ∧
        NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
          (fun a : Fin W.outputDim × Fin W.outputDim => fun x : Fin 3 → ℤ =>
            W.eval a.1 (correlationInput (x 0) (x 1)) *
              star (W.eval a.2 (correlationInput (x 0) (x 1 + x 2))))
          (fun a : Fin V.outputDim × Fin V.outputDim × Fin V.outputDim => fun x : Fin 3 → ℤ =>
            star ((V.eval a.1 (cubicTrilinearInput (x 0) (x 1) (x 2)) *
              V.eval a.2.1 (cubicTrilinearInput (x 0) (x 2) (x 1))) *
                V.eval a.2.2 (cubicTrilinearInput (x 0) (x 2) (x 2)))) := by
  obtain ⟨A, _, hmulti⟩ := exists_symmetric_multilinearization 2
  obtain ⟨B, _, htranslate⟩ := exists_cubic_translation_equivalence
  obtain ⟨D, _, htrans⟩ := NativeIntegerVectorEquivalence.exists_trans_budget
  obtain ⟨F, _, hcancel⟩ := NativeIntegerVectorEquivalence.exists_cancel_left_tensor_budget
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let T := (U + Polynomial.C B) ^ B
  let R := U + T + 2
  let S := (R + Polynomial.C D) ^ D
  let P := 3 * U + S + 2
  let G := (P + Polynomial.C F) ^ F
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + S + P + G)
  refine ⟨C, hC, ?_⟩
  intro p W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let u := (p + A) ^ A
  let t := (u + B) ^ B
  let r := u + t + 2
  let s := (r + D) ^ D
  let v := 3 * u + s + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hG : 0 ≤ (v + F) ^ F := by positivity
  have hsum : u + t + s + v + (v + F) ^ F ≤ (p + C) ^ C := by
    simpa [X, U, T, R, S, P, G, u, t, r, s, v, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hfinal : (v + F) ^ F ≤ (p + C) ^ C := by linarith
  obtain ⟨V, hdim, hsymm, E⟩ := hmulti (mixedCorrelationDegree 2)
    (by rw [Fin.sum_univ_two]; rfl) W
  let base : Fin 2 → ((Fin 3 → ℤ) →+ ℤ) := fun j => {
    toFun := fun x => correlationInput (x 0) (x 1) j
    map_zero' := by fin_cases j <;> rfl
    map_add' := fun x y => by fin_cases j <;> rfl }
  let shifted : Fin 2 → ((Fin 3 → ℤ) →+ ℤ) := fun j => {
    toFun := fun x => correlationInput (x 0) (x 1 + x 2) j
    map_zero' := by fin_cases j <;> rfl
    map_add' := fun x y => by
      fin_cases j
      · rfl
      · change (x 1 + y 1) + (x 2 + y 2) = (x 1 + x 2) + (y 1 + y 2)
        ring }
  have E₀ : NativeIntegerVectorEquivalence 2 u
      (fun i => fun x : Fin 3 → ℤ => W.eval i (correlationInput (x 0) (x 1)))
      (fun k x => V.eval k (cubicTrilinearInput (x 0) (x 1) (x 1))) := by
    have E' := E.linearPullbackHom base
    change NativeIntegerVectorEquivalence 2 u
      (fun i => fun x : Fin 3 → ℤ => W.eval i (correlationInput (x 0) (x 1)))
      (fun k x => V.eval k (fun j => correlationInput (x 0) (x 1) j.1)) at E'
    simpa only [← cubicTrilinearInput_diagonal] using E'
  have E₁ : NativeIntegerVectorEquivalence 2 u
      (fun i => fun x : Fin 3 → ℤ => W.eval i (correlationInput (x 0) (x 1 + x 2)))
      (fun k x => V.eval k (cubicTrilinearInput (x 0) (x 1 + x 2) (x 1 + x 2))) := by
    have E' := E.linearPullbackHom shifted
    change NativeIntegerVectorEquivalence 2 u
      (fun i => fun x : Fin 3 → ℤ => W.eval i (correlationInput (x 0) (x 1 + x 2)))
      (fun k x => V.eval k (fun j => correlationInput (x 0) (x 1 + x 2) j.1)) at E'
    simpa only [← cubicTrilinearInput_diagonal] using E'
  have hE := htrans hr (E₁.mono (by dsimp [r]; linarith))
    ((htranslate V).mono (by dsimp [r]; linarith))
    (fun x => V.unit_eval (cubicTrilinearInput (x 0) (x 1 + x 2) (x 1 + x 2)))
  have hdim₃ : (Fintype.card (Fin V.outputDim × Fin V.outputDim × Fin V.outputDim) : ℝ) ≤ Real.exp v := by
    have heq : (Fintype.card (Fin V.outputDim × Fin V.outputDim × Fin V.outputDim) : ℝ) =
        (V.outputDim : ℝ) ^ 3 := by
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      ring
    rw [heq]
    calc
      _ ≤ Real.exp u ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) V.output_bound 3
      _ = Real.exp (3 * u) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp v := Real.exp_le_exp.mpr (by dsimp [v]; linarith)
  have hderiv := hcancel
    (d := fun a : Fin V.outputDim × Fin V.outputDim × Fin V.outputDim => fun x : Fin 3 → ℤ =>
      (V.eval a.1 (cubicTrilinearInput (x 0) (x 1) (x 2)) *
        V.eval a.2.1 (cubicTrilinearInput (x 0) (x 2) (x 1))) *
          V.eval a.2.2 (cubicTrilinearInput (x 0) (x 2) (x 2)))
    hv (E₀.mono (by change u ≤ 3 * u + s + 2; linarith))
    (hE.mono (by change s ≤ 3 * u + s + 2; linarith))
    (fun x => V.unit_eval (cubicTrilinearInput (x 0) (x 1) (x 1))) hdim₃
  refine ⟨V.mono huC, ?_, hsymm, E.mono huC, hderiv.mono hfinal⟩
  change V.dim ≤ 8 * W.dim
  exact hdim

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

noncomputable def cubicMixedDerivative {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) p)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 3 → ℤ) : ℂ :=
  W.eval a.1 (correlationInput (x 0) (x 1)) *
    star (W.eval a.2 (correlationInput (x 0) (x 1 + x 2)))

noncomputable def cubicTrilinearTriple {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
    (a : Fin V.outputDim × Fin V.outputDim × Fin V.outputDim) (x : Fin 3 → ℤ) : ℂ :=
  star ((V.eval a.1 (cubicTrilinearInput (x 0) (x 1) (x 2)) *
    V.eval a.2.1 (cubicTrilinearInput (x 0) (x 2) (x 1))) *
      V.eval a.2.2 (cubicTrilinearInput (x 0) (x 2) (x 2)))

theorem cubicTrilinearTriple_unit {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
    (x : Fin 3 → ℤ) : ∑ a, ‖V.cubicTrilinearTriple a x‖ ^ 2 = 1 := by
  simp only [cubicTrilinearTriple, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, V.unit_eval, mul_one]

theorem cubic_trilinear_sample_correlation {p q r v : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) p)
    (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) q)
    (E : NativeIntegerVectorEquivalence 2 r W.cubicMixedDerivative V.cubicTrilinearTriple)
    (S : Finset ℤ) (h k : ℤ) (i j : Fin W.outputDim) (f : ℤ → ℂ)
    (hcorr : Real.exp (-v) ≤ ‖𝔼 n ∈ S, f n *
      star (W.eval i (correlationInput h n) * star (W.eval j (correlationInput h (n + k))))‖) :
    ∃ (a : Fin V.outputDim × Fin V.outputDim × Fin V.outputDim)
      (l : Fin (E.selectedExpansion (i, j) a).count),
      Real.exp (-(v + 2 * r)) ≤ ‖𝔼 n ∈ S,
        f n * (V.eval a.1 (cubicTrilinearInput h n k) *
          V.eval a.2.1 (cubicTrilinearInput h k n)) *
            star (((E.selectedExpansion (i, j) a).test l).eval ![h, n, k])‖ := by
  obtain ⟨a, l, hal⟩ := E.transfer_sample_correlation S (fun n => ![h, n, k]) (i, j) f
    (fun n _ => V.cubicTrilinearTriple_unit _) (by
      simpa only [cubicMixedDerivative, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using hcorr)
  let T := (E.selectedExpansion (i, j) a).test l
  let F (n : ℤ) := f n * (V.eval a.1 (cubicTrilinearInput h n k) *
    V.eval a.2.1 (cubicTrilinearInput h k n)) * star (T.eval ![h, n, k])
  have heq : (𝔼 n ∈ S, f n * star (V.cubicTrilinearTriple a ![h, n, k]) *
      star (T.eval ![h, n, k])) =
      (𝔼 n ∈ S, F n) * V.eval a.2.2 (cubicTrilinearInput h k k) := by
    rw [Finset.expect_mul]
    apply Finset.expect_congr rfl
    intro n _
    simp only [F, cubicTrilinearTriple, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, star_star]
    ring
  change Real.exp (-(v + 2 * r)) ≤ ‖𝔼 n ∈ S,
    f n * star (V.cubicTrilinearTriple a ![h, n, k]) * star (T.eval ![h, n, k])‖ at hal
  rw [heq, norm_mul] at hal
  refine ⟨a, l, hal.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left (V.norm_eval _ _) (norm_nonneg _)).trans_eq (mul_one _)

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_cubic_trilinear_intervals :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
          ∃ E : NativeIntegerVectorEquivalence 2 r M.cubicMixedDerivative V.cubicTrilinearTriple,
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, t.2 ∈ H ∧ ∃ (branch : Bool) (a len : ℕ),
                0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
                Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
                ∃ (b : Fin V.outputDim × Fin V.outputDim × Fin V.outputDim)
                  (l : Fin (E.selectedExpansion (i, i) b).count),
                  Real.exp (-((p + C) ^ C)) ≤
                    ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                      multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 (n : ZMod N) *
                        (V.eval b.1 (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)) *
                          V.eval b.2.1 (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch))) *
                            star (((E.selectedExpansion (i, i) b).test l).eval
                              ![(t.2.val : ℤ), n, cyclicBranchOffset t.1 branch])‖ := by
  obtain ⟨A, _, hinterval⟩ := exists_cubic_exchanged_intervals
  obtain ⟨B, _, hcompare⟩ := NativeMultidegreeNilcharacter.exists_cubic_trilinear_derivative_equivalence
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  let R := (P + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + 3 * R + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + A) ^ A
  let r := (q + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsum : q + 3 * r + 2 ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  have htransferC : q + 2 * r ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hHdense, M, i, χ, hcorr, Q, hQ, hQdense, hQcorr⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  obtain ⟨V, hdim, hsymm, hdiag, hderiv⟩ := hcompare M
  let E : NativeIntegerVectorEquivalence 2 r M.cubicMixedDerivative V.cubicTrilinearTriple := hderiv
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hrC, ?_, hsymm, hdiag.mono hrC,
    r, hr, hrC, E, i, χ, ?_, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (sq_nonneg _)).trans hQdense
  · intro t ht
    obtain ⟨htH, branch, a, len, hlen, hlenN, hshort, hc, hvolume⟩ := hQcorr t ht
    obtain ⟨b, l, hbl⟩ := M.cubic_trilinear_sample_correlation V E
      (Finset.Ico (a : ℤ) (a + len)) (t.2.val : ℤ) (cyclicBranchOffset t.1 branch) i i
      (fun n => multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 (n : ZMod N)) hc
    refine ⟨htH, branch, a, len, hlen, hlenN, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvolume, b, l, ?_⟩
    have hswap (n : ℤ) := V.eval_cubicTrilinearInput_swap hsymm b.2.1
      (t.2.val : ℤ) (cyclicBranchOffset t.1 branch) n
    have hfinal := (Real.exp_le_exp.mpr (neg_le_neg htransferC)).trans hbl
    simp_rw [hswap] at hfinal
    exact hfinal

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_cubic_fixed_trilinear_intervals :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
          ∃ E : NativeIntegerVectorEquivalence 2 r M.cubicMixedDerivative V.cubicTrilinearTriple,
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (b : Fin V.outputDim × Fin V.outputDim × Fin V.outputDim)
              (l : Fin (E.selectedExpansion (i, i) b).count),
            ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, t.2 ∈ H ∧ ∃ a len : ℕ,
                0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
                Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
                Real.exp (-((p + C) ^ C)) ≤
                  ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                    multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 (n : ZMod N) *
                      (V.eval b.1 (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)) *
                        V.eval b.2.1 (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch))) *
                          star (((E.selectedExpansion (i, i) b).test l).eval
                            ![(t.2.val : ℤ), n, cyclicBranchOffset t.1 branch])‖ := by
  obtain ⟨A, _, hinterval⟩ := exists_cubic_trilinear_intervals
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsum : 3 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, r, hr, hrq, E,
    i, χ, hcorr, Q, hQ, hQdense, hQcorr⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let K := Σ b : Fin V.outputDim × Fin V.outputDim × Fin V.outputDim,
    Fin (E.selectedExpansion (i, i) b).count
  let R (t : ZMod N × ZMod N) (_ : Unit) (c : Bool × K) : Prop :=
    t.2 ∈ H ∧ ∃ a len : ℕ,
      0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
        ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
          multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 (n : ZMod N) *
            (V.eval c.2.1.1 (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 c.1)) *
              V.eval c.2.1.2.1 (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 c.1))) *
                star (((E.selectedExpansion (i, i) c.2.1).test c.2.2).eval
                  ![(t.2.val : ℤ), n, cyclicBranchOffset t.1 c.1])‖
  have hchoice : ∀ t ∈ Q, ∀ u, ∃ c, R t u c := by
    intro t ht _
    obtain ⟨htH, branch, a, len, hlen, hNlen, hshort, hvol, b, l, hcor⟩ := hQcorr t ht
    exact ⟨(branch, ⟨b, l⟩), htH, a, len, hlen, hNlen, hshort, hvol, hcor⟩
  have hK : (Fintype.card K : ℝ) ≤ Real.exp (2 * r) := by
    simp only [K, Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    calc
      _ ≤ ∑ _b : Fin V.outputDim × Fin V.outputDim × Fin V.outputDim, Real.exp r :=
        Finset.sum_le_sum fun b _ => (E.selectedExpansion (i, i) b).count_bound
      _ = (Fintype.card (Fin V.outputDim × Fin V.outputDim × Fin V.outputDim) : ℝ) * Real.exp r := by simp
      _ ≤ Real.exp r * Real.exp r := mul_le_mul_of_nonneg_right E.right_dimension (Real.exp_nonneg _)
      _ = Real.exp (2 * r) := by rw [← Real.exp_add]; congr 1; ring
  have hcount : (Fintype.card (Bool × K) : ℝ) ≤ Real.exp (2 * q + 1) := by
    rw [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ ≤ Real.exp 1 * Real.exp (2 * r) := mul_le_mul
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) hK (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (1 + 2 * r) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨c, S, hSQ, hS, hSdense, hfixed⟩ := exists_large_fixed_choices Q hQ R hchoice hcount
  have hsize : Real.exp (-(2 * q + 1)) * (Q.card : ℝ) ≤ (S.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hSdense
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hqC, ?_, hsymm, hdiag.mono hqC,
    r, hr, hrq.trans hqC, E, i, χ, ?_, (c ()).1, (c ()).2.1, (c ()).2.2, S, hS, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · calc
      _ ≤ Real.exp (-(3 * q + 1)) * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (sq_nonneg _)
      _ = Real.exp (-(2 * q + 1)) * (Real.exp (-q) * (N : ℝ) ^ 2) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(2 * q + 1)) * (Q.card : ℝ) :=
        mul_le_mul_of_nonneg_left hQdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨htH, a, len, hlen, hNlen, hshort, hvol, hcor⟩ := hfixed t ht ()
    exact ⟨htH, a, len, hlen, hNlen, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hcor⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_cubic_separated_intervals :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i' j' : Fin V.outputDim) (A B : ℤ → ℤ → ℂ),
              (∀ h n, ‖A h n‖ ≤ 1) ∧ (∀ n k, ‖B n k‖ ≤ 1) ∧
              ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
                Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
                ∀ t ∈ Q, t.2 ∈ H ∧ ∃ a len : ℕ,
                  0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
                  Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
                  Real.exp (-((p + C) ^ C)) ≤
                    ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                      (multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 (n : ZMod N) *
                        (V.eval i' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)) *
                          V.eval j' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)))) *
                            A (t.2.val : ℤ) n * B n (cyclicBranchOffset t.1 branch)‖ := by
  obtain ⟨a, _, hinterval⟩ := exists_cubic_fixed_trilinear_intervals
  obtain ⟨b, _, habsorb⟩ := exists_absorb_cubic_error
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsum : q + r + 2 ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hr, hsum]
  have hrC : r ≤ (p + C) ^ C := by linarith only [hq, hsum]
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, u, hu, huq, E,
    i, χ, hcorr, branch, v, l, Q, hQ, hQdense, hQcorr⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let T := (E.selectedExpansion (i, i) v).test l
  have hT : T.ComplexityLE q := ((E.selectedExpansion (i, i) v).complexity l).mono huq
  have hdata (t : Q) := hQcorr t.val t.property
  choose hmem start len hlen hend hshort hvol hcor using hdata
  let I (t : Q) := Finset.Ico (start t : ℤ) (start t + len t)
  let F (t : Q) (n : ℤ) :=
    multiplicativeDerivative (multiplicativeDerivative f t.val.1) t.val.2 (n : ZMod N) *
      (V.eval v.1 (cubicTrilinearInput (t.val.2.val : ℤ) n (cyclicBranchOffset t.val.1 branch)) *
        V.eval v.2.1 (cubicTrilinearInput (t.val.2.val : ℤ) n (cyclicBranchOffset t.val.1 branch)))
  let : Nonempty Q := hQ.to_subtype
  have hI (t : Q) : (I t).Nonempty := Finset.nonempty_Ico.mpr (by
    have hh := hlen t
    change (start t : ℤ) < start t + len t
    omega)
  have hF (t : Q) (n : ℤ) : ‖F t n‖ ≤ 1 := by
    simp only [F, norm_mul]
    exact (mul_le_of_le_one_left (by positivity)
      (multiplicativeDerivative_norm_le_one _ (multiplicativeDerivative_norm_le_one f hf t.val.1)
        t.val.2 _)).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval _ _)).trans (V.norm_eval _ _))
  obtain ⟨A, B, hA, hB, S, _, hS, hSdense, hScor⟩ :=
    habsorb T hT Finset.univ Finset.univ_nonempty I (fun t _ => hI t)
      (fun t => (t.val.2.val : ℤ)) (fun t => cyclicBranchOffset t.val.1 branch) F
      (fun t _ n _ => hF t n) (fun t _ => hcor t)
  let e : Q ↪ ZMod N × ZMod N := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map e
  have hQ' : Q'.Nonempty := hS.map
  have hsize : Real.exp (-r) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hqC, ?_, hsymm, hdiag.mono hqC,
    E.mono (huq.trans hqC), i, χ, ?_, branch, v.1, v.2.1, A, B, hA, hB, Q', hQ', ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · calc
      _ ≤ Real.exp (-(q + r)) * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [hsum])) (sq_nonneg _)
      _ = Real.exp (-r) * (Real.exp (-q) * (N : ℝ) ^ 2) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-r) * (Q.card : ℝ) := mul_le_mul_of_nonneg_left hQdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    exact ⟨hmem t', start t', len t', hlen t', hend t', hshort t',
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hvol t'),
      (Real.exp_le_exp.mpr (neg_le_neg hrC)).trans (hScor t' ht')⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cubic_common_interval :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i' j' : Fin V.outputDim) (A B : ℤ → ℤ → ℂ),
              (∀ h n, ‖A h n‖ ≤ 1) ∧ (∀ n k, ‖B n k‖ ≤ 1) ∧
              ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
                Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
                ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
                  Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
                  ∀ t ∈ Q, t.2 ∈ H ∧ Real.exp (-((p + C) ^ C)) ≤
                    ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                      (multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 (n : ZMod N) *
                        (V.eval i' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)) *
                          V.eval j' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)))) *
                            A (t.2.val : ℤ) n * B n (cyclicBranchOffset t.1 branch)‖ := by
  obtain ⟨c, _, hseparated⟩ := exists_cubic_separated_intervals
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (5 * P + 12)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsum : 5 * q + 12 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hsum]
  have hgridC : 2 * q + 8 ≤ (p + C) ^ C := by linarith only [hq, hsum]
  have hcC : q + 1 ≤ (p + C) ^ C := by linarith only [hq, hsum]
  have hdC : 5 * q + 10 ≤ (p + C) ^ C := by linarith only [hsum]
  have hNpos : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, i, χ, hcorr,
    branch, i', j', A, B, hA, hB, Q, hQ, hQdense, hQcorr⟩ :=
    hseparated hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  have hdata (t : Q) := hQcorr t.val t.property
  choose hmem start len hlen hend hshort hvol hcor using hdata
  let F (t : Q) (n : ℤ) :=
    (multiplicativeDerivative (multiplicativeDerivative f t.val.1) t.val.2 (n : ZMod N) *
      (V.eval i' (cubicTrilinearInput (t.val.2.val : ℤ) n (cyclicBranchOffset t.val.1 branch)) *
        V.eval j' (cubicTrilinearInput (t.val.2.val : ℤ) n (cyclicBranchOffset t.val.1 branch)))) *
          A (t.val.2.val : ℤ) n * B n (cyclicBranchOffset t.val.1 branch)
  let : Nonempty Q := hQ.to_subtype
  have hF (t : Q) (n : ℤ) : ‖F t n‖ ≤ 1 := by
    simp only [F, norm_mul]
    have hderiv := multiplicativeDerivative_norm_le_one _
      (multiplicativeDerivative_norm_le_one f hf t.val.1) t.val.2 (n : ZMod N)
    have hv := (mul_le_of_le_one_left (norm_nonneg _)
      (V.norm_eval i' (cubicTrilinearInput (t.val.2.val : ℤ) n
        (cyclicBranchOffset t.val.1 branch)))).trans
        (V.norm_eval j' (cubicTrilinearInput (t.val.2.val : ℤ) n (cyclicBranchOffset t.val.1 branch)))
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((mul_le_of_le_one_left (norm_nonneg _)
        ((mul_le_of_le_one_left (by positivity) hderiv).trans hv)).trans (hA _ _))).trans (hB _ _)
  obtain ⟨S, _, hS, hSdense, a, d, hd, had, hshortd, hvold, hScor⟩ :=
    exists_common_integer_interval hq ((Real.exp_le_exp.mpr hgridC).trans hN)
      Finset.univ Finset.univ_nonempty start len (fun t _ => hend t) (fun t _ => hshort t)
      (fun t _ => (le_div_iff₀ hNpos).mp (hvol t)) F (fun t _ n => hF t n) (fun t _ => hcor t)
  let e : Q ↪ ZMod N × ZMod N := ⟨Subtype.val, Subtype.val_injective⟩
  let Q' := S.map e
  have hQ' : Q'.Nonempty := hS.map
  have hsize : Real.exp (-(4 * q + 10)) * (Q.card : ℝ) ≤ (Q'.card : ℝ) := by
    simpa only [Q', Finset.card_map, Finset.card_univ, Fintype.card_coe] using hSdense
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hqC, ?_, hsymm, hdiag.mono hqC,
    E.mono hqC, i, χ, ?_, branch, i', j', A, B, hA, hB, a, d, hd, had, hshortd, ?_, Q', hQ', ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · apply (le_div_iff₀ hNpos).mpr
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcC))
      hNpos.le).trans hvold
  · calc
      _ ≤ Real.exp (-(5 * q + 10)) * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hdC)) (sq_nonneg _)
      _ = Real.exp (-(4 * q + 10)) * (Real.exp (-q) * (N : ℝ) ^ 2) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(4 * q + 10)) * (Q.card : ℝ) :=
        mul_le_mul_of_nonneg_left hQdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    exact ⟨hmem t', (Real.exp_le_exp.mpr (neg_le_neg hcC)).trans (hScor t' ht')⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cubic_positive_trilinear :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i' j' : Fin V.outputDim) (A B D : ℤ → ℤ → ℂ),
              (∀ h n, ‖A h n‖ ≤ 1) ∧ (∀ n k, ‖B n k‖ ≤ 1) ∧ (∀ h k, ‖D h k‖ ≤ 1) ∧
              ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
                Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
                Real.exp (-((p + C) ^ C)) ≤
                  (𝔼 t : ZMod N × ZMod N, 𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                    f ((n + (t.2.val : ℤ) + cyclicBranchOffset t.1 branch : ℤ) : ZMod N) *
                      (V.eval i' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)) *
                        V.eval j' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch))) *
                          A (t.2.val : ℤ) n * B n (cyclicBranchOffset t.1 branch) *
                            D (t.2.val : ℤ) (cyclicBranchOffset t.1 branch)).re := by
  obtain ⟨c, _, hcommon⟩ := exists_cubic_common_interval
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsum : 2 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hsum]
  have htwo : 2 * q ≤ (p + C) ^ C := by linarith only [hsum]
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, i, χ, hcorr,
    branch, i', j', A₀, B₀, hA₀, hB₀, a, len, hlen, hend, hshort, hvol, Q, _, hQdense, hQcorr⟩ :=
    hcommon hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  obtain ⟨A, B, hA, hB, habsorb⟩ := exists_cubic_diagonal_weights f hf A₀ B₀ hA₀ hB₀
  let F (t : ZMod N × ZMod N) (n : ℤ) :=
    f ((n + (t.2.val : ℤ) + cyclicBranchOffset t.1 branch : ℤ) : ZMod N) *
      (V.eval i' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)) *
        V.eval j' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch))) *
          A (t.2.val : ℤ) n * B n (cyclicBranchOffset t.1 branch)
  have heq (t : ZMod N × ZMod N) (n : ℤ) :
      (multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 (n : ZMod N) *
        (V.eval i' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)) *
          V.eval j' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)))) *
            A₀ (t.2.val : ℤ) n * B₀ n (cyclicBranchOffset t.1 branch) = F t n := by
    simpa only [F, cyclicBranchOffset_zmod, Int.cast_natCast, ZMod.natCast_zmod_val] using
      habsorb (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)
        (V.eval i' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)) *
          V.eval j' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)))
  have hrow (t : ZMod N × ZMod N) (ht : t ∈ Q) :
      Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F t n‖ := by
    simpa only [heq] using (hQcorr t ht).2
  have hdensity : Real.exp (-q) * Fintype.card (ZMod N × ZMod N) ≤ (Q.card : ℝ) := by
    simpa only [Fintype.card_prod, ZMod.card, Nat.cast_mul, pow_two] using hQdense
  obtain ⟨w, hw, _, hpositive⟩ := exists_dense_row_phase_alignment Q
    (Finset.Ico (a : ℤ) (a + len)) F (Real.exp_nonneg (-q)) hdensity hrow
  let D (h k : ℤ) := w ((k : ZMod N), (h : ZMod N))
  have hD (t : ZMod N × ZMod N) :
      D (t.2.val : ℤ) (cyclicBranchOffset t.1 branch) = w t := by
    simp only [D, cyclicBranchOffset_zmod, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hscore : Real.exp (-(2 * q)) ≤
      (𝔼 t, 𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), w t * F t n).re := by
    have hpow : Real.exp (-(2 * q)) = Real.exp (-q) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hpow]
    exact hpositive
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hqC, ?_, hsymm, hdiag.mono hqC,
    E.mono hqC, i, χ, ?_, branch, i', j', A, B, D, hA, hB, (fun h k => hw _),
    a, len, hlen, hend, hshort, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol
  · change Real.exp (-((p + C) ^ C)) ≤
      (𝔼 t, 𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        F t n * D (t.2.val : ℤ) (cyclicBranchOffset t.1 branch)).re
    simpa only [hD, mul_comm] using (Real.exp_le_exp.mpr (neg_le_neg htwo)).trans hscore

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cubic_cyclic_positive_trilinear :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i' j' : Fin V.outputDim) (A B D : ℤ → ℤ → ℂ),
              (∀ h n, ‖A h n‖ ≤ 1) ∧ (∀ n k, ‖B n k‖ ≤ 1) ∧ (∀ h k, ‖D h k‖ ≤ 1) ∧
              ∃ a len : ℕ, 0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
                Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
                (∀ h n : ℤ, (n : ZMod N) ∉ cyclicInterval (a : ZMod N) len → A h n = 0) ∧
                Real.exp (-((p + C) ^ C)) ≤
                  (𝔼 t : ZMod N × ZMod N, 𝔼 n : ZMod N,
                    f (n + t.2 + t.1) *
                      (V.eval i' (cubicTrilinearInput (t.2.val : ℤ) (n.val : ℤ) (cyclicBranchOffset t.1 branch)) *
                        V.eval j' (cubicTrilinearInput (t.2.val : ℤ) (n.val : ℤ) (cyclicBranchOffset t.1 branch))) *
                          A (t.2.val : ℤ) (n.val : ℤ) * B (n.val : ℤ) (cyclicBranchOffset t.1 branch) *
                            D (t.2.val : ℤ) (cyclicBranchOffset t.1 branch)).re := by
  obtain ⟨c, _, hinterval⟩ := exists_cubic_positive_trilinear
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsum : 2 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hsum]
  have htwo : 2 * q ≤ (p + C) ^ C := by linarith only [hsum]
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, i, χ, hcorr,
    branch, i', j', A, B, D, hA, hB, hD, a, len, hlen, hend, hshort, hvol, hpositive⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let I := cyclicInterval (a : ZMod N) len
  let A' (h n : ℤ) := A h n * finiteIndicator I (n : ZMod N)
  let F (t : ZMod N × ZMod N) (n : ℤ) :=
    f ((n + (t.2.val : ℤ) + cyclicBranchOffset t.1 branch : ℤ) : ZMod N) *
      (V.eval i' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch)) *
        V.eval j' (cubicTrilinearInput (t.2.val : ℤ) n (cyclicBranchOffset t.1 branch))) *
          A (t.2.val : ℤ) n * B n (cyclicBranchOffset t.1 branch) *
            D (t.2.val : ℤ) (cyclicBranchOffset t.1 branch)
  let G (t : ZMod N × ZMod N) (n : ZMod N) :=
    f (n + t.2 + t.1) *
      (V.eval i' (cubicTrilinearInput (t.2.val : ℤ) (n.val : ℤ) (cyclicBranchOffset t.1 branch)) *
        V.eval j' (cubicTrilinearInput (t.2.val : ℤ) (n.val : ℤ) (cyclicBranchOffset t.1 branch))) *
          A' (t.2.val : ℤ) (n.val : ℤ) * B (n.val : ℤ) (cyclicBranchOffset t.1 branch) *
            D (t.2.val : ℤ) (cyclicBranchOffset t.1 branch)
  have hrow (t : ZMod N × ZMod N) : (𝔼 n, G t n) =
      (((len : ℝ) / N : ℝ) : ℂ) * (𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F t n) := by
    calc
      _ = 𝔼 n : ZMod N, finiteIndicator I n * F t (n.val : ℤ) := by
        apply Finset.expect_congr rfl
        intro n _
        simp only [G, F, A', Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val,
          cyclicBranchOffset_zmod]
        ring
      _ = _ := cyclicInterval_zeroExtension_average a len hend hshort (F t)
  have hmean : (𝔼 t, 𝔼 n, G t n).re =
      (len : ℝ) / N * (𝔼 t, 𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), F t n).re := by
    simp_rw [hrow]
    rw [← Finset.mul_expect]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hqC, ?_, hsymm, hdiag.mono hqC,
    E.mono hqC, i, χ, ?_, branch, i', j', A', B, D, ?_, hB, hD,
    a, len, hlen, hend, hshort, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · intro h n
    dsimp only [A']
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hA h n)).trans (finiteIndicator_norm_le_one I _)
  · exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol
  · intro h n hn
    simp only [A', I, finiteIndicator, hn, ite_false, mul_zero]
  · change Real.exp (-((p + C) ^ C)) ≤ (𝔼 t, 𝔼 n, G t n).re
    rw [hmean]
    calc
      _ ≤ Real.exp (-(2 * q)) := Real.exp_le_exp.mpr (neg_le_neg htwo)
      _ = Real.exp (-q) * Real.exp (-q) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul hvol hpositive (Real.exp_nonneg _) (by positivity)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def NativeMultidegreeNilcharacter.cubicCyclicPair {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
    {N : ℕ} [NeZero N] (branch : Bool) (i j : Fin V.outputDim) (h n k : ZMod N) : ℂ :=
  V.eval i (cubicTrilinearInput (h.val : ℤ) (n.val : ℤ) (cyclicBranchOffset k branch)) *
    V.eval j (cubicTrilinearInput (h.val : ℤ) (n.val : ℤ) (cyclicBranchOffset k branch))

theorem exists_cubic_reflected_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i' j' : Fin V.outputDim) (z : ZMod N)
              (b : (ZMod N × ZMod N) → ZMod N → ℂ), (∀ t h, ‖b t h‖ ≤ 1) ∧
              let K := V.cubicCyclicPair branch i' j'
              Real.exp (-((p + C) ^ C)) ≤
                (𝔼 t : ZMod N × ZMod N, 𝔼 h, 𝔼 h',
                  (K h (z - h - h') t.1 * star (K h (z - h - h') t.2)) *
                    star (K h' (z - h - h') t.1 * star (K h' (z - h - h') t.2)) *
                      b t h * star (b t h')).re := by
  obtain ⟨c, _, hcyclic⟩ := exists_cubic_cyclic_positive_trilinear
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hsum : 4 * q + 2 ≤ (p + C) ^ C := by
    simpa [P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hsum]
  have hfour : 4 * q ≤ (p + C) ^ C := by linarith only [hsum]
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, i, χ, hcorr,
    branch, i', j', A, B, D, hA, hB, hD, a, len, hlen, hend, hshort, hvol,
    hsupport, hpositive⟩ := hcyclic hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let K := V.cubicCyclicPair (N := N) branch i' j'
  let A' (h n : ZMod N) := A (h.val : ℤ) (n.val : ℤ)
  let B' (n k : ZMod N) := B (n.val : ℤ) (cyclicBranchOffset k branch)
  let D' (h k : ZMod N) := D (h.val : ℤ) (cyclicBranchOffset k branch)
  have hinput : Real.exp (-q) ≤
      ‖𝔼 k, 𝔼 h, 𝔼 n, f (n + h + k) * K h n k * A' h n * B' n k * D' h k‖ := by
    simpa only [expect_prod_split, K, NativeMultidegreeNilcharacter.cubicCyclicPair,
      A', B', D'] using hpositive.trans (Complex.re_le_norm _)
  obtain ⟨z, b, hb, hreflect⟩ := exists_cubic_reflected_correlation K f A' B' D' hf
    (fun h n => hA _ _) (fun n k => hB _ _) (fun h k => hD _ _)
  have hbound := (pow_le_pow_left₀ (Real.exp_nonneg (-q)) hinput 4).trans hreflect
  have hpower : Real.exp (-q) ^ 4 = Real.exp (-(4 * q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [hpower] at hbound
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hqC, ?_, hsymm, hdiag.mono hqC,
    E.mono hqC, i, χ, ?_, branch, i', j', z, b, hb, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg hfour)).trans hbound

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def NativeMultidegreeNilcharacter.cubicIntegerPair {p : ℝ}
    (V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
    (i j : Fin V.outputDim) (h n k : ℤ) : ℂ :=
  V.eval i (cubicTrilinearInput h n k) * V.eval j (cubicTrilinearInput h n k)

theorem exists_cubic_unwrapped_reflection :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i' j' : Fin V.outputDim) (z : ZMod N) (carry : Fin 3)
              (A B : (ZMod N × ZMod N) → ℤ → ℂ),
              (∀ t h, ‖A t h‖ ≤ 1) ∧ (∀ t h, ‖B t h‖ ≤ 1) ∧
              let K := V.cubicIntegerPair i' j'
              let c : ℤ := z.val + (carry.val : ℤ) * N
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 t : ZMod N × ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
                  (K h.val (c - h.val - h'.val) (cyclicBranchOffset t.1 branch) *
                    star (K h.val (c - h.val - h'.val) (cyclicBranchOffset t.2 branch))) *
                    star (K h'.val (c - h.val - h'.val) (cyclicBranchOffset t.1 branch) *
                      star (K h'.val (c - h.val - h'.val) (cyclicBranchOffset t.2 branch))) *
                        A t h.val * B t h'.val‖ := by
  obtain ⟨c, _, hreflection⟩ := exists_cubic_reflected_model
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * P + 10)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + c) ^ c
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hcost : 2 * q + 10 ≤ (p + C) ^ C := by
    simpa [P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hq, hcost]
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, i, χ, hcorr,
    branch, i', j', z, b, hb, hreflect⟩ :=
    hreflection hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let K := V.cubicIntegerPair i' j'
  let R (t : ZMod N × ZMod N) (h n : ℤ) :=
    K h n (cyclicBranchOffset t.1 branch) * star (K h n (cyclicBranchOffset t.2 branch))
  have hK (h n k : ℤ) : ‖K h n k‖ ≤ 1 := by
    dsimp only [K, NativeMultidegreeNilcharacter.cubicIntegerPair]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval _ _)).trans (V.norm_eval _ _)
  have hR (t : ZMod N × ZMod N) (h n : ℤ) : ‖R t h n‖ ≤ 1 := by
    dsimp only [R]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hK _ _ _)).trans (hK _ _ _)
  have hc : Real.exp (-q) ≤ ‖𝔼 t, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
      R t h.val (z - h - h').val * star (R t h'.val (z - h - h').val) *
        b t h * star (b t h')‖ := by
    simpa only [R, K, NativeMultidegreeNilcharacter.cubicIntegerPair,
      NativeMultidegreeNilcharacter.cubicCyclicPair] using hreflect.trans (Complex.re_le_norm _)
  obtain ⟨carry, A, B, hA, hB, hunwrapped⟩ :=
    exists_unwrapped_family_reflected_correlation hq R R hR hR z b hb hc
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hqC, ?_, hsymm, hdiag.mono hqC,
    E.mono hqC, i, χ, ?_, branch, i', j', z, carry, A, B, hA, hB, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hunwrapped

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cubic_anchored_reflection :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i' j' : Fin V.outputDim) (z : ZMod N) (carry : Fin 3)
              (A B : ZMod N → ℤ → ℂ) (D : ℤ → ℤ → ℂ),
              (∀ k h, ‖A k h‖ ≤ 1) ∧ (∀ k h, ‖B k h‖ ≤ 1) ∧ (∀ h h', ‖D h h'‖ ≤ 1) ∧
              let K := V.cubicIntegerPair i' j'
              let c : ℤ := z.val + (carry.val : ℤ) * N
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 k : ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
                  K h.val (c - h.val - h'.val) (cyclicBranchOffset k branch) *
                    star (K h'.val (c - h.val - h'.val) (cyclicBranchOffset k branch)) *
                      A k h.val * B k h'.val * D h.val h'.val‖ := by
  obtain ⟨C, hC, hunwrap⟩ := exists_cubic_unwrapped_reflection
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, i, χ, hcorr,
    branch, i', j', z, carry, A, B, hA, hB, hunwrapped⟩ := hunwrap hp hN f hf hGowers
  let K := V.cubicIntegerPair i' j'
  let c : ℤ := z.val + (carry.val : ℤ) * N
  let F (k k' : ZMod N) := 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
    (K h.val (c - h.val - h'.val) (cyclicBranchOffset k branch) *
      star (K h.val (c - h.val - h'.val) (cyclicBranchOffset k' branch))) *
      star (K h'.val (c - h.val - h'.val) (cyclicBranchOffset k branch) *
        star (K h'.val (c - h.val - h'.val) (cyclicBranchOffset k' branch))) *
          A (k, k') h.val * B (k, k') h'.val
  change Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 t : ZMod N × ZMod N, F t.1 t.2‖ at hunwrapped
  rw [expect_prod_split, Finset.expect_comm] at hunwrapped
  have hmean : Real.exp (-((p + C) ^ C)) ≤ 𝔼 k', ‖𝔼 k, F k k'‖ :=
    hunwrapped.trans (RCLike.norm_expect_le (K := ℂ))
  obtain ⟨k₀, _, hk₀⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  let A' (k : ZMod N) (h : ℤ) := A (k, k₀) h
  let B' (k : ZMod N) (h : ℤ) := B (k, k₀) h
  let D (h h' : ℤ) := star (K h (c - h - h') (cyclicBranchOffset k₀ branch)) *
    K h' (c - h - h') (cyclicBranchOffset k₀ branch)
  have hK (h n k : ℤ) : ‖K h n k‖ ≤ 1 := by
    dsimp only [K, NativeMultidegreeNilcharacter.cubicIntegerPair]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (V.norm_eval _ _)).trans (V.norm_eval _ _)
  have heq : (𝔼 k, F k k₀) =
      𝔼 k : ZMod N, 𝔼 h : ZMod N, 𝔼 h' : ZMod N,
        K h.val (c - h.val - h'.val) (cyclicBranchOffset k branch) *
          star (K h'.val (c - h.val - h'.val) (cyclicBranchOffset k branch)) *
            A' k h.val * B' k h'.val * D h.val h'.val := by
    apply Finset.expect_congr rfl
    intro k _
    apply Finset.expect_congr rfl
    intro h _
    apply Finset.expect_congr rfl
    intro h' _
    simp only [A', B', D, star_mul, star_star]
    ring
  refine ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, i, χ, hcorr,
    branch, i', j', z, carry, A', B', D, (fun k h => hA _ _), (fun k h => hB _ _), ?_, ?_⟩
  · intro h h'
    dsimp only [D]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hK _ _ _)).trans (hK _ _ _)
  · rwa [heq] at hk₀

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cubic_antisymmetric_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) ((p + C) ^ C),
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 ((p + C) ^ C)
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i' j' : Fin V.outputDim × Fin V.outputDim) (A B D : ℤ → ℤ → ℂ),
              (∀ h k, ‖A h k‖ ≤ 1) ∧ (∀ h k, ‖B h k‖ ≤ 1) ∧ (∀ h y, ‖D h y‖ ≤ 1) ∧
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 k : ZMod N, 𝔼 h : ZMod N, 𝔼 y : ZMod N,
                  V.cubicAntisymmetricPair i' j' h.val y.val (cyclicBranchOffset k branch) *
                    A h.val (cyclicBranchOffset k branch) *
                      B y.val (cyclicBranchOffset k branch) * D h.val y.val‖ := by
  obtain ⟨a, _, hanchor⟩ := exists_cubic_anchored_reflection
  obtain ⟨b, _, htransfer⟩ := exists_cubic_antisymmetric_transfer
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hsum : q + (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqb : 0 ≤ (q + b) ^ b := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith only [hsum, hqb]
  have hfinal : (q + b) ^ b ≤ (p + C) ^ C := by linarith only [hsum, hq]
  obtain ⟨H, hH, hHdense, M, V, hdim, hsymm, hdiag, E, i, χ, hcorr,
    branch, i₀, j₀, z₀, carry, A, B, D, hA, hB, hD, hreflection⟩ :=
    hanchor hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let c : ℤ := z₀.val + (carry.val : ℤ) * N
  let x (u : ZMod N × ZMod N × ZMod N) : ℤ := u.2.1.val
  let y (u : ZMod N × ZMod N × ZMod N) : ℤ := u.2.2.val
  let z (u : ZMod N × ZMod N × ZMod N) : ℤ := cyclicBranchOffset u.1 branch
  let A₀ (h k : ℤ) := A (k : ZMod N) h
  let B₀ (h k : ℤ) := B (k : ZMod N) h
  have hsource (h y k : ℤ) :
      V.cubicReflectionSource c (i₀, i₀) ![h, y, k] *
        V.cubicReflectionSource c (j₀, j₀) ![h, y, k] =
      V.cubicIntegerPair i₀ j₀ h (c - h - y) k * star (V.cubicIntegerPair i₀ j₀ y (c - h - y) k) := by
    simp only [NativeMultidegreeNilcharacter.cubicReflectionSource,
      NativeMultidegreeNilcharacter.cubicIntegerPair, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, star_mul]
    ring
  have hinput : Real.exp (-q) ≤ ‖𝔼 u : ZMod N × ZMod N × ZMod N,
      (V.cubicReflectionSource c (i₀, i₀) ![x u, y u, z u] *
        V.cubicReflectionSource c (j₀, j₀) ![x u, y u, z u]) *
          A₀ (x u) (z u) * B₀ (y u) (z u) * D (x u) (y u)‖ := by
    simpa only [hsource, expect_prod_split, x, y, z, c, A₀, B₀,
      cyclicBranchOffset_zmod] using hreflection
  obtain ⟨i', j', A', B', D', hA', hB', hD', hc⟩ := htransfer V c i₀ j₀
    (Finset.univ : Finset (ZMod N × ZMod N × ZMod N)) Finset.univ_nonempty x y z A₀ B₀ D
    (fun h k => hA _ _) (fun h k => hB _ _) hD hinput
  refine ⟨H, hH, ?_, M.mono hqC, V.mono hqC, ?_, hsymm, hdiag.mono hqC,
    E.mono hqC, i, χ, ?_, branch, i', j', A', B', D', hA', hB', hD', ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hHdense
  · change V.dim ≤ 8 * M.dim
    exact hdim
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · simpa only [expect_prod_split, x, y, z,
      NativeMultidegreeNilcharacter.cubicAntisymmetricPair,
      NativeMultidegreeNilcharacter.mono_eval] using
      (Real.exp_le_exp.mpr (neg_le_neg hfinal)).trans hc

end Erdos3

end

end OAI
