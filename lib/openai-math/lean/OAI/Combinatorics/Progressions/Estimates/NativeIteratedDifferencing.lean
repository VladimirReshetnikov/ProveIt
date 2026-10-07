import OAI.Combinatorics.Progressions.Estimates.FiniteTupleFibers
import OAI.Combinatorics.Progressions.Polynomial.PositiveDegreeCyclicDifference

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mean_row_correlation_sq_le_derivative_correlation {H G : Type*}
    [Fintype H] [Nonempty H] [AddCommGroup G] [Fintype G]
    (f g : H → G → ℂ) :
    (𝔼 h, ‖𝔼 n, f h n * star (g h n)‖) ^ 2 ≤
      𝔼 k, 𝔼 h, ‖𝔼 n, multiplicativeDerivative (f h) k n *
        star (multiplicativeDerivative (g h) k n)‖ := by
  let F (h : H) (n : G) := f h n * star (g h n)
  have hid (h : H) :
      (𝔼 k, 𝔼 n, multiplicativeDerivative (f h) k n *
        star (multiplicativeDerivative (g h) k n)).re =
          ‖𝔼 n, f h n * star (g h n)‖ ^ 2 := by
    have heq (k n : G) : crossDerivative (F h) (F h) k n =
        multiplicativeDerivative (f h) k n * star (multiplicativeDerivative (g h) k n) := by
      simp only [crossDerivative, multiplicativeDerivative, F, star_mul, star_star]
      ring
    have hh := congrArg Complex.re (expect_crossDerivative (F h) (F h))
    simpa only [heq, mul_star_re_eq_norm_sq, F] using hh
  have hrow (h : H) : ‖𝔼 n, f h n * star (g h n)‖ ^ 2 ≤
      𝔼 k, ‖𝔼 n, multiplicativeDerivative (f h) k n *
        star (multiplicativeDerivative (g h) k n)‖ := by
    rw [← hid h, expect_re]
    exact Finset.expect_le_expect (fun k _ => Complex.re_le_norm _)
  calc
    _ ≤ 𝔼 h, ‖𝔼 n, f h n * star (g h n)‖ ^ 2 := expect_square_le _
    _ ≤ 𝔼 h, 𝔼 k, ‖𝔼 n, multiplicativeDerivative (f h) k n *
        star (multiplicativeDerivative (g h) k n)‖ :=
      Finset.expect_le_expect (fun h _ => hrow h)
    _ = _ := Finset.expect_comm _ _ _

theorem mean_row_correlation_sq_le_approximated_derivatives {H G : Type*}
    [Fintype H] [Nonempty H] [AddCommGroup G] [Fintype G]
    (f g : H → G → ℂ) (K : G → H → G → ℂ) (hf : ∀ h n, ‖f h n‖ ≤ 1)
    {ε : ℝ} (herr : ∀ k h, (𝔼 n, ‖multiplicativeDerivative (g h) k n - K k h n‖) ≤ ε) :
    (𝔼 h, ‖𝔼 n, f h n * star (g h n)‖) ^ 2 ≤
      (𝔼 k, 𝔼 h, ‖𝔼 n, multiplicativeDerivative (f h) k n * star (K k h n)‖) + ε := by
  have hrow (k : G) (h : H) :
      ‖𝔼 n, multiplicativeDerivative (f h) k n * star (multiplicativeDerivative (g h) k n)‖ ≤
        ‖𝔼 n, multiplicativeDerivative (f h) k n * star (K k h n)‖ + ε := by
    have hfn (n : G) : ‖multiplicativeDerivative (f h) k n‖ ≤ 1 := by
      rw [multiplicativeDerivative, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf h n)).trans (hf h (n + k))
    have he := (norm_correlation_sub_le_mean (multiplicativeDerivative (f h) k)
      (multiplicativeDerivative (g h) k) (K k h) hfn).trans (herr k h)
    have ht := norm_le_norm_add_norm_sub
      (𝔼 n, multiplicativeDerivative (f h) k n * star (K k h n))
      (𝔼 n, multiplicativeDerivative (f h) k n * star (multiplicativeDerivative (g h) k n))
    rw [norm_sub_rev] at ht
    linarith
  apply (mean_row_correlation_sq_le_derivative_correlation f g).trans
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun k _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun h _ => hrow k h))
  simpa only [Finset.expect_add_distrib, Fintype.expect_const] using hm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem mean_mul_error_le_separate {X : Type*} [Fintype X]
    (u v U V : X → ℂ) {B ε δ : ℝ} (hB : 0 ≤ B)
    (hv : ∀ x, ‖v x‖ ≤ 1) (hU : ∀ x, ‖U x‖ ≤ B)
    (huerr : (𝔼 x, ‖u x - U x‖) ≤ ε) (hverr : (𝔼 x, ‖v x - V x‖) ≤ δ) :
    (𝔼 x, ‖u x * v x - U x * V x‖) ≤ ε + B * δ := by
  have hpoint (x : X) :
      ‖u x * v x - U x * V x‖ ≤ ‖u x - U x‖ + B * ‖v x - V x‖ := by
    calc
      _ = ‖(u x - U x) * v x + U x * (v x - V x)‖ := by congr 1; ring
      _ ≤ ‖u x - U x‖ * ‖v x‖ + ‖U x‖ * ‖v x - V x‖ := by
        simpa only [norm_mul] using norm_add_le ((u x - U x) * v x) (U x * (v x - V x))
      _ ≤ _ := add_le_add (mul_le_of_le_one_right (norm_nonneg _) (hv x))
        (mul_le_mul_of_nonneg_right (hU x) (norm_nonneg _))
  calc
    _ ≤ 𝔼 x, (‖u x - U x‖ + B * ‖v x - V x‖) :=
      Finset.expect_le_expect (fun x _ => hpoint x)
    _ = (𝔼 x, ‖u x - U x‖) + B * (𝔼 x, ‖v x - V x‖) := by
      rw [Finset.expect_add_distrib, ← Finset.mul_expect]
    _ ≤ _ := add_le_add huerr (mul_le_mul_of_nonneg_left hverr hB)

theorem mean_row_correlation_sq_le_product_derivatives {H G : Type*}
    [Fintype H] [Nonempty H] [AddCommGroup G] [Fintype G]
    (f u v : H → G → ℂ) (U V : G → H → G → ℂ) {B ε δ : ℝ}
    (hf : ∀ h n, ‖f h n‖ ≤ 1) (hv : ∀ h n, ‖v h n‖ ≤ 1) (hB : 0 ≤ B)
    (hU : ∀ k h n, ‖U k h n‖ ≤ B)
    (huerr : ∀ k h, (𝔼 n, ‖multiplicativeDerivative (u h) k n - U k h n‖) ≤ ε)
    (hverr : ∀ k h, (𝔼 n, ‖multiplicativeDerivative (v h) k n - V k h n‖) ≤ δ) :
    (𝔼 h, ‖𝔼 n, f h n * star (u h n * v h n)‖) ^ 2 ≤
      (𝔼 k, 𝔼 h, ‖𝔼 n, multiplicativeDerivative (f h) k n * star (U k h n * V k h n)‖) +
        (ε + B * δ) := by
  apply mean_row_correlation_sq_le_approximated_derivatives f
    (fun h n => u h n * v h n) (fun k h n => U k h n * V k h n) hf
  intro k h
  have heq : multiplicativeDerivative (fun n => u h n * v h n) k =
      fun n => multiplicativeDerivative (u h) k n * multiplicativeDerivative (v h) k n := by
    funext n
    simp only [multiplicativeDerivative, star_mul]
    ring
  rw [heq]
  apply mean_mul_error_le_separate _ _ _ _ hB _ (hU k h) (huerr k h) (hverr k h)
  intro n
  simp only [multiplicativeDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hv h n)).trans (hv h (n + k))

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_cyclic_second_difference_models_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {I : Type*} [Fintype I]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {p e : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Fin 2 => 1)),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card I : ℝ) ≤ Real.exp p → 0 ≤ e →
      ∀ {N : ℕ} [NeZero N], Real.exp (e + 16) ≤ (N : ℝ) →
      ∀ (i j : I) (k : ZMod N), ∃ K : (Fin 2 → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + e + C) ^ C) K) ∧
        ∀ h : ℤ, (𝔼 n : ZMod N,
          ‖cyclicSecondDifference (V.test g i).eval (V.test g j).eval k h n -
            K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, htranslate⟩ := exists_integer_translation_equivalence_budget s
  obtain ⟨B, _, happrox⟩ := exists_cyclicSecondDifference_approximation_degree s hs
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C A) ^ A + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d D p e V g hp hD hI he N _ hN i j k
  let r := (p + A) ^ A
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hmodels (t : ℤ) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r
      (integerSecondDifference (V.test g i).eval (V.test g j).eval t)) := by
    have E := (htranslate D V g hp hD hI 0 ![0, t]).expansion i j
    change Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r
      (fun x => (V.test g i).eval (x + 0) * star ((V.test g j).eval (x + ![0, t])))) at E
    have hshift (x : Fin 2 → ℤ) : x + ![0, t] = ![x 0, x 1 + t] := by
      funext a
      fin_cases a <;> simp
    change Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r
      (fun x => (V.test g i).eval x * star ((V.test g j).eval ![x 0, x 1 + t])))
    simpa only [add_zero, hshift] using E
  have hcost : (r + e + B) ^ B ≤ (p + e + C) ^ C := by
    have hbase : r ≤ (p + e + A) ^ A := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have hb : ((p + e + A) ^ A + (p + e) + B) ^ B ≤ (p + e + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget (p + e) (by linarith)
    exact (pow_le_pow_left₀ (by positivity) (by linarith) B).trans hb
  obtain ⟨K, ⟨E⟩, herr⟩ := happrox hr he hN (V.test g i).eval (V.test g j).eval
    (fun x => (V.test g i).norm_eval_le x) (fun x => (V.test g j).norm_eval_le x) hmodels k
  exact ⟨K, ⟨E.mono hcost⟩, herr⟩

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_differenced_rows_degree (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ZMod N → ℂ, (∀ h n, ‖f h n‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        f h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ K : ZMod N → (Fin 2 → ℤ) → ℂ,
        (∀ k, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s ((p + C) ^ C) (K k))) ∧
        Real.exp (-((p + C) ^ C)) ≤ (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
          multiplicativeDerivative (f h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) := by
  obtain ⟨A, _, hunit⟩ := exists_unit_vertical_mean_row_model (s + 1)
  obtain ⟨B, _, hcyclic⟩ := UnitVerticalObservable.exists_cyclic_second_difference_models_degree s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * Q + 2 + Polynomial.C B) ^ B + 3 * Q + 20)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN f hf hcorr
  classical
  let q := (p + A) ^ A
  let e := 2 * q + 2
  let r := (3 * q + 2 + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he : 0 ≤ e := by dsimp [e]; linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : r + 3 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  have heC : e ≤ (p + C) ^ C := by dsimp [e]; linarith
  have hN' : Real.exp (e + 16) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by dsimp [e]; linarith)).trans hN
  obtain ⟨m, _, hmcard, V, hD, hVcorr⟩ := hunit D T hp hT
    (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)]) f hf hcorr
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hmcard
  have hmodels (k : ZMod N) : ∃ K : (Fin 2 → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r K) ∧
      ∀ h : ℤ, (𝔼 n : ZMod N,
        ‖cyclicSecondDifference (V.test T.orbit 0).eval (V.test T.orbit 0).eval k h n -
          K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
    have hh := hcyclic D V T.orbit hq hD hcard he hN' 0 0 k
    have hbudgeteq : ((p + A) ^ A + e + B) ^ B = r := by
      change (q + e + B) ^ B = (3 * q + 2 + B) ^ B
      congr 1
      dsimp [e]
      ring
    simpa only [hbudgeteq] using hh
  choose K hK herror using hmodels
  let g (h n : ZMod N) := (V.test T.orbit 0).eval ![(h.val : ℤ), (n.val : ℤ)]
  have hd := mean_row_correlation_sq_le_approximated_derivatives f g
    (fun k h n => K k ![(h.val : ℤ), (n.val : ℤ)]) hf
    (ε := Real.exp (-e)) (by
      intro k h
      simpa only [g, multiplicativeDerivative, cyclicSecondDifference] using herror k h.val)
  have hlarge : Real.exp (-(2 * q)) ≤
      (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        multiplicativeDerivative (f h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) +
          Real.exp (-e) := by
    have hsquare := (pow_le_pow_left₀ (Real.exp_nonneg (-q)) hVcorr 2).trans hd
    have hexp : Real.exp (-q) ^ 2 = Real.exp (-(2 * q)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rwa [hexp] at hsquare
  have htwo : 2 * Real.exp (-e) ≤ Real.exp (-(2 * q)) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-e) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
  refine ⟨K, fun k => ⟨(Classical.choice (hK k)).mono hrC⟩, ?_⟩
  apply (Real.exp_le_exp.mpr (neg_le_neg heC)).trans
  linarith

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_differenced_scalar_expansions (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (T : D.Niltest (fun _ : Unit => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 n, f n * star (T.evalCyclic N (fun _ => n))‖ →
      ∃ K : ZMod N → (Unit → ℤ) → ℂ,
        (∀ k, Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) s ((p + C) ^ C) (K k))) ∧
        Real.exp (-((p + C) ^ C)) ≤ (𝔼 k : ZMod N, ‖𝔼 n : ZMod N,
          multiplicativeDerivative f k n * star (K k (fun _ => (n.val : ℤ)))‖) := by
  obtain ⟨A, _, hunit⟩ := RationalFilteredNilmanifold.exists_unit_vertical_mean_row_model (s + 1)
  obtain ⟨B, _, hcyclic⟩ :=
    RationalFilteredNilmanifold.UnitVerticalObservable.exists_cyclic_second_difference_models_degree s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * Q + 2 + Polynomial.C B) ^ B + 3 * Q + 20)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN f hf hcorr
  classical
  let projection : Unit → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let U := T.linearPullbackHom projection
  have hU (n : ZMod N) : U.eval ![0, (n.val : ℤ)] = T.evalCyclic N (fun _ => n) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom]
    rfl
  let q := (p + A) ^ A
  let e := 2 * q + 2
  let r := (3 * q + 2 + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he : 0 ≤ e := by dsimp [e]; linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : r + 3 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  have heC : e ≤ (p + C) ^ C := by dsimp [e]; linarith
  have hN' : Real.exp (e + 16) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by dsimp [e]; linarith)).trans hN
  obtain ⟨m, _, hmcard, V, hD, hVcorr⟩ := hunit D U hp hT
    (fun (_ : Unit) (n : ZMod N) => ![0, (n.val : ℤ)]) (fun _ => f) (fun _ => hf)
    (by simpa only [hU, Fintype.expect_const] using hcorr)
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hmcard
  have hmodels (k : ZMod N) : ∃ K : (Fin 2 → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) s r K) ∧
      (𝔼 n : ZMod N, ‖cyclicSecondDifference (V.test U.orbit 0).eval
        (V.test U.orbit 0).eval k 0 n - K ![0, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
    obtain ⟨K, hK, herr⟩ := hcyclic D V U.orbit hq hD hcard he hN' 0 0 k
    have hbudgeteq : ((p + A) ^ A + e + B) ^ B = r := by
      change (q + e + B) ^ B = (3 * q + 2 + B) ^ B
      congr 1
      dsimp [e]
      ring
    exact ⟨K, by simpa only [hbudgeteq] using hK, herr 0⟩
  choose K hK herror using hmodels
  let embedding : Fin 2 → ((Unit → ℤ) →+ ℤ) := fun j =>
    if j = 0 then 0 else
      { toFun := fun x => x (), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hemb (x : Unit → ℤ) : (fun j => embedding j x) = ![0, x ()] := by
    funext j
    fin_cases j <;> simp [embedding]
  let g (n : ZMod N) := (V.test U.orbit 0).eval ![0, (n.val : ℤ)]
  have hc : Real.exp (-q) ≤ ‖𝔼 n : ZMod N, f n * star (g n)‖ := by
    simpa only [Fintype.expect_const] using hVcorr
  have hd := mean_row_correlation_sq_le_approximated_derivatives
    (fun _ : Unit => f) (fun _ : Unit => g)
    (fun k _ n => K k ![0, (n.val : ℤ)]) (fun _ => hf)
    (ε := Real.exp (-e)) (by
      intro k _
      simpa only [g, multiplicativeDerivative, cyclicSecondDifference] using herror k)
  simp only [Fintype.expect_const] at hd
  have hlarge : Real.exp (-(2 * q)) ≤
      (𝔼 k : ZMod N, ‖𝔼 n : ZMod N,
        multiplicativeDerivative f k n * star (K k ![0, (n.val : ℤ)])‖) + Real.exp (-e) := by
    have hsq := (pow_le_pow_left₀ (Real.exp_nonneg (-q)) hc 2).trans hd
    have hexp : Real.exp (-q) ^ 2 = Real.exp (-(2 * q)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rwa [hexp] at hsq
  have htwo : 2 * Real.exp (-e) ≤ Real.exp (-(2 * q)) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-e) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
  refine ⟨fun k x => K k ![0, x ()], ?_, ?_⟩
  · intro k
    have E := ((Classical.choice (hK k)).linearPullbackHom embedding).mono hrC
    simpa only [hemb] using (show Nonempty _ from ⟨E⟩)
  · apply (Real.exp_le_exp.mpr (neg_le_neg heC)).trans
    linarith

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_many_native_derivative_correlations (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      Nonempty (NativeVectorCorrelation (s + 1) N p (fun _ : Unit => f)) →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∀ h ∈ H, Nonempty (NativeVectorCorrelation s N ((p + C) ^ C)
          (fun _ : Unit => multiplicativeDerivative f h)) := by
  obtain ⟨A, _, hdifference⟩ := exists_differenced_scalar_expansions s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (4 * Q + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf ⟨V⟩
  classical
  let q := (p + A) ^ A
  let t := 3 * q + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have htotal : 4 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by dsimp [t]; linarith
  have htqC : t + q ≤ (p + C) ^ C := by dsimp [t]; linarith
  obtain ⟨K, hK, hmean⟩ := hdifference V.model V.test hp V.complexity
    ((Real.exp_le_exp.mpr hqC).trans hN) f hf V.correlation
  let c (k : ZMod N) := ‖𝔼 n : ZMod N,
    multiplicativeDerivative f k n * star (K k (fun _ => (n.val : ℤ)))‖
  let z (k : ZMod N) := Real.exp (-(2 * q)) * c k
  have hcap (k : ZMod N) : c k ≤ Real.exp (2 * q) := by
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (multiplicativeDerivative_norm_le_one f hf k n)).trans
        ((Classical.choice (hK k)).norm_eval_le _)
  have hzcap (k : ZMod N) : z k ≤ 1 := by
    calc
      _ ≤ Real.exp (-(2 * q)) * Real.exp (2 * q) :=
        mul_le_mul_of_nonneg_left (hcap k) (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hzmean : Real.exp (-(3 * q)) ≤ 𝔼 k, z k := by
    change Real.exp (-(3 * q)) ≤ 𝔼 k, Real.exp (-(2 * q)) * c k
    rw [← Finset.mul_expect]
    have heq : Real.exp (-(3 * q)) = Real.exp (-(2 * q)) * Real.exp (-q) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hmean (Real.exp_nonneg _)
  obtain ⟨H, hHsize, hHcorr⟩ :=
    exists_dense_level_set z (Real.exp_nonneg (-(3 * q))) hzcap hzmean
  have hhalf : Real.exp (-t) ≤ Real.exp (-(3 * q)) / 2 := by
    apply (Real.exp_le_exp.mpr (by dsimp [t]; linarith : -t ≤ -(3 * q) - 1)).trans
    exact exp_sub_one_le_half_exp (-(3 * q))
  have hdense : Real.exp (-t) * N ≤ (H.card : ℝ) := by
    simpa only [ZMod.card] using
      (mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg (Fintype.card (ZMod N)))).trans hHsize
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hH : H.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le (by positivity : 0 < Real.exp (-t) * (N : ℝ)) hdense
  refine ⟨H, hH, (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg htC)) (Nat.cast_nonneg N)).trans hdense, ?_⟩
  intro k hk
  have hzle : z k ≤ c k := mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (by linarith))
  have hc : Real.exp (-t) ≤ c k := hhalf.trans ((hHcorr k hk).trans hzle)
  let E := Classical.choice (hK k)
  obtain ⟨i, hi⟩ := E.select_sample_correlation Finset.univ (fun (n : ZMod N) (_ : Unit) => (n.val : ℤ))
    (multiplicativeDerivative f k) hc
  exact ⟨{
    L := E.L i
    dim := E.dim i
    model := E.model i
    test := E.test i
    complexity := (E.complexity i).mono hqC
    coordinate := ()
    correlation := (Real.exp_le_exp.mpr (neg_le_neg htqC)).trans hi }⟩

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_univariate_cyclic_difference_models (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {I : Type*} [Fintype I]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {p e : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card I : ℝ) ≤ Real.exp p → 0 ≤ e →
      ∀ {N : ℕ} [NeZero N], Real.exp (e + 16) ≤ (N : ℝ) →
      ∀ (i j : I) (k : ZMod N), ∃ K : (Unit → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) s ((p + e + C) ^ C) K) ∧
        (𝔼 n : ZMod N,
          ‖(V.test g i).eval (fun _ => (n.val : ℤ)) *
              star ((V.test g j).eval (fun _ => ((n + k).val : ℤ))) -
            K (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e) := by
  obtain ⟨C, hC, htwo⟩ := exists_cyclic_second_difference_models_degree s hs
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d D p e V g hp hD hI he N _ hN i j k
  let A : Unit → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let g₂ := ((V.test g i).linearPullbackHom A).orbit
  have heval (l : I) (x : Fin 2 → ℤ) :
      (V.test g₂ l).eval x = (V.test g l).eval (fun _ => x 1) := by
    change ((V.test g l).linearPullbackHom A).eval x = _
    exact (V.test g l).eval_linearPullbackHom A x
  obtain ⟨K, ⟨E⟩, herr⟩ := htwo D V g₂ hp hD hI he hN i j k
  let B : Fin 2 → ((Unit → ℤ) →+ ℤ) :=
    ![0, { toFun := fun x => x (), map_zero' := rfl, map_add' := fun _ _ => rfl }]
  have hB (x : Unit → ℤ) : (fun l => B l x) = ![0, x ()] := by
    funext l
    fin_cases l <;> rfl
  refine ⟨fun x => K ![0, x ()], ?_, ?_⟩
  · exact ⟨by simpa only [hB] using E.linearPullbackHom B⟩
  · simpa only [cyclicSecondDifference, heval, Matrix.cons_val_one, Matrix.cons_val_zero] using herr 0

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_iterated_native_derivative_correlations (k d : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      Nonempty (NativeVectorCorrelation (k + d) N p (fun _ : Unit => f)) →
      ∃ Q : Finset (Fin d → ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ d ≤ (Q.card : ℝ) ∧
        ∀ u ∈ Q, Nonempty (NativeVectorCorrelation k N ((p + C) ^ C)
          (fun _ : Unit => cubeProduct f (List.ofFn u))) := by
  induction d with
  | zero =>
    refine ⟨2, le_rfl, ?_⟩
    intro N _ p hp _ f _ ⟨V⟩
    classical
    have hq : 0 ≤ (p + 2) ^ 2 := sq_nonneg _
    have hpq : p ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
    refine ⟨Finset.univ, Finset.univ_nonempty, ?_, ?_⟩
    · simpa using (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hq))
    · intro u _
      have hfun : (fun _ : Unit => cubeProduct f (List.ofFn u)) = (fun _ : Unit => f) := by
        funext _ x
        simp only [List.ofFn_zero, cubeProduct_nil]
      rw [hfun]
      exact ⟨V.mono hpq⟩
  | succ d ih =>
    obtain ⟨a, _, hstep⟩ := exists_many_native_derivative_correlations (k + d) (by omega)
    obtain ⟨b, _, hiter⟩ := ih
    let X : Polynomial ℕ := Polynomial.X
    let P := (X + Polynomial.C a) ^ a
    let R := (P + Polynomial.C b) ^ b
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
    refine ⟨C, hC, ?_⟩
    intro N _ p hp hN f hf hc
    classical
    let q := (p + a) ^ a
    let r := (q + b) ^ b
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hsum : q + r ≤ (p + C) ^ C := by
      simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
    have hqC : q ≤ (p + C) ^ C := by linarith
    have hrC : r ≤ (p + C) ^ C := by linarith
    obtain ⟨H, hH, hHdense, hHcorr⟩ := hstep hp ((Real.exp_le_exp.mpr hqC).trans hN)
      f hf (by simpa only [Nat.add_assoc] using hc)
    have hdata (h : H) := hiter hq ((Real.exp_le_exp.mpr hrC).trans hN)
      (multiplicativeDerivative f h.val) (multiplicativeDerivative_norm_le_one f hf h.val)
      (hHcorr h.val h.property)
    choose K _hK hKdense hKcorr using hdata
    obtain ⟨Q, hQdense, hQmem⟩ := dense_tuple_fibers d H K (Real.exp_nonneg (-r))
      (by simpa only [ZMod.card] using hHdense)
      (fun h => by simpa only [ZMod.card] using hKdense h)
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    have hQ : Q.Nonempty := by
      apply Finset.card_pos.mp
      exact_mod_cast lt_of_lt_of_le
        (by positivity : 0 < Real.exp (-q) * Real.exp (-r) * (Fintype.card (ZMod N) : ℝ) ^ (d + 1)) hQdense
    refine ⟨Q, hQ, ?_, ?_⟩
    · have heq : Real.exp (-(q + r)) = Real.exp (-q) * Real.exp (-r) := by rw [neg_add, Real.exp_add]
      have hsmall := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (neg_le_neg hsum)) (pow_nonneg (Nat.cast_nonneg N) (d + 1))
      rw [heq] at hsmall
      exact hsmall.trans (by simpa only [ZMod.card] using hQdense)
    · intro u hu
      obtain ⟨h, hh, htail⟩ := (hQmem u).mp hu
      have hlist : List.ofFn u = h.val :: List.ofFn (Fin.tail u) := by
        rw [List.ofFn_succ, ← hh]
        rfl
      obtain ⟨V⟩ := hKcorr h (Fin.tail u) htail
      have hfun : (fun _ : Unit => cubeProduct f (List.ofFn u)) =
          (fun _ : Unit => cubeProduct (multiplicativeDerivative f h.val)
            (List.ofFn (Fin.tail u))) := by
        funext _ x
        rw [hlist, cubeProduct_cons_eq_derivative]
      rw [hfun]
      exact ⟨V.mono hrC⟩

end Erdos3

end

end OAI
