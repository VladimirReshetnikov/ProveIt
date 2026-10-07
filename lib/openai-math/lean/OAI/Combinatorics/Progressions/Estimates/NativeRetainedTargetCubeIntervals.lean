/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CubeSignalAlgebra
import OAI.Combinatorics.Progressions.Estimates.FamilyDerivativeCorrelation
import OAI.Combinatorics.Progressions.Fourier.NativeMixedFourierProfiles

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_cyclic_derivative_integer_interval {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (R : ℤ → ℂ) (h : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hR : ∀ n, ‖R n‖ ≤ 1)
    (hcorr : ρ ≤ ‖𝔼 x : ZMod N, f x * star (R x.val * star (R (x + h).val))‖) :
    ∃ (branch : Bool) (a len : ℕ), 0 < len ∧ a + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      ρ / 20 ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        f (n : ZMod N) * star (R n * star (R (n + cyclicBranchOffset h branch)))‖ ∧
      ρ / 20 ≤ (len : ℝ) / N := by
  let shifts : Fin 2 → ZMod N := ![0, h]
  let u : Fin 2 → ℤ → ℂ := ![R, fun n => star (R n)]
  have heval (x : ZMod N) : translatedCyclicProduct shifts u x = R x.val * star (R (x + h).val) := by
    simp only [translatedCyclicProduct, shifts, u, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_add, add_comm h x]
  have hcap (x : ZMod N) : ‖translatedCyclicProduct shifts u x‖ ≤ 1 := by
    rw [heval, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hR _)).trans (hR _)
  have hc : ρ ≤ ‖finiteCorrelation Finset.univ f (translatedCyclicProduct shifts u)‖ := by
    simpa only [finiteCorrelation, heval] using hcorr
  obtain ⟨a, hlen, hN, hshort, hcor, hvol⟩ := exists_correlating_integer_product_interval
    shifts u f hρ (by norm_num : (0 : ℝ) < 1) hf hcap hc
  norm_num only [Fintype.card_fin, Nat.cast_ofNat, mul_one] at hcor hvol
  let len := intervalCutUpper (commonCyclicCuts shifts) N a.val - a.val
  have haN : a.val < N := by omega
  have hoff : cyclicTranslationOffset (shifts 0) a.val = 0 := by
    simp [shifts, cyclicTranslationOffset, Nat.not_le.mpr haN]
  let branch := decide (N - h.val ≤ a.val)
  have hprod (n : ℤ) : (∏ i, u i (n + cyclicTranslationOffset (shifts i) a.val)) =
      R n * star (R (n + cyclicBranchOffset h branch)) := by
    rw [Fin.prod_univ_two, hoff]
    simp only [u, shifts, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero,
      cyclicTranslationOffset_eq_branch, branch]
  refine ⟨branch, a.val, len, hlen, hN, hshort, ?_, hvol⟩
  simpa only [finiteCorrelation, hprod] using hcor

theorem exists_cyclic_derivative_integer_interval_re {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (R : ℤ → ℂ) (h : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hR : ∀ n, ‖R n‖ ≤ 1)
    (hcorr : ρ ≤ (𝔼 x : ZMod N, f x * star (R x.val * star (R (x + h).val))).re) :
    ∃ (branch : Bool) (a len : ℕ), 0 < len ∧ a + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      ρ / 20 ≤ (𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        f (n : ZMod N) * star (R n * star (R (n + cyclicBranchOffset h branch)))).re ∧
      ρ / 20 ≤ (len : ℝ) / N := by
  let shifts : Fin 2 → ZMod N := ![0, h]
  let u : Fin 2 → ℤ → ℂ := ![R, fun n => star (R n)]
  have heval (x : ZMod N) : translatedCyclicProduct shifts u x = R x.val * star (R (x + h).val) := by
    simp only [translatedCyclicProduct, shifts, u, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, zero_add, add_comm h x]
  have hcap (x : ZMod N) : ‖translatedCyclicProduct shifts u x‖ ≤ 1 := by
    rw [heval, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hR _)).trans (hR _)
  have hc : ρ ≤ (finiteCorrelation Finset.univ f (translatedCyclicProduct shifts u)).re := by
    simpa only [finiteCorrelation, heval] using hcorr
  obtain ⟨a, hlen, hN, hshort, hcor, hvol⟩ := exists_re_correlating_integer_product_interval
    shifts u f hρ (by norm_num : (0 : ℝ) < 1) hf hcap hc
  norm_num only [Fintype.card_fin, Nat.cast_ofNat, mul_one] at hcor hvol
  let len := intervalCutUpper (commonCyclicCuts shifts) N a.val - a.val
  have haN : a.val < N := by omega
  have hoff : cyclicTranslationOffset (shifts 0) a.val = 0 := by
    simp [shifts, cyclicTranslationOffset, Nat.not_le.mpr haN]
  let branch := decide (N - h.val ≤ a.val)
  have hprod (n : ℤ) : (∏ i, u i (n + cyclicTranslationOffset (shifts i) a.val)) =
      R n * star (R (n + cyclicBranchOffset h branch)) := by
    rw [Fin.prod_univ_two, hoff]
    simp only [u, shifts, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero,
      cyclicTranslationOffset_eq_branch, branch]
  refine ⟨branch, a.val, len, hlen, hN, hshort, ?_, hvol⟩
  simpa only [finiteCorrelation, hprod] using hcor

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_exchanged_intervals :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim, ∀ t ∈ Q,
            ∃ (branch : Bool) (a len : ℕ), 0 < len ∧ a + len ≤ N ∧
              2 * ((len : ℤ) - 1) < N ∧
              Real.exp (-((p + C) ^ C)) ≤
                (𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                  multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 (n : ZMod N) *
                    star (M.eval i (correlationInput (t.2.val : ℤ) n) *
                      star (M.eval i (correlationInput (t.2.val : ℤ) (n + cyclicBranchOffset t.1 branch))))).re ∧
              Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N := by
  obtain ⟨A, _, hexchange⟩ := exists_quadratic_exchanged_correlations
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + 5)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have htotal : q + 5 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have h20 : (20 : ℝ) ≤ Real.exp 5 :=
    (by norm_num : (20 : ℝ) ≤ 2 ^ 5).trans (two_pow_le_exp_of_le 5 le_rfl)
  have hsmall : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-q) / 20 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 20)).mpr
    calc
      _ ≤ Real.exp (-((p + C) ^ C)) * Real.exp 5 :=
        mul_le_mul_of_nonneg_left h20 (Real.exp_nonneg _)
      _ = Real.exp (-((p + C) ^ C) + 5) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨Q, hQ, hdense, M, i, hcorr⟩ := hexchange hp f hf hG
  refine ⟨Q, hQ, ?_, M.mono hqC, i, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (sq_nonneg _)).trans hdense
  · intro t ht
    let R (n : ℤ) := M.eval i (correlationInput (t.2.val : ℤ) n)
    let w (x : ZMod N) := multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 x
    have hRval (x : ZMod N) : R (x.val : ℤ) = M.evalCyclic N i (correlationInput t.2 x) := by
      change M.eval i (correlationInput (t.2.val : ℤ) (x.val : ℤ)) =
        M.eval i (fun j => ((correlationInput t.2 x j).val : ℤ))
      apply congrArg (M.eval i)
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have hw (x : ZMod N) : ‖w x‖ ≤ 1 :=
      multiplicativeDerivative_norm_le_one _ (multiplicativeDerivative_norm_le_one f hf t.1) t.2 x
    have hc : Real.exp (-q) ≤
        (𝔼 x : ZMod N, w x * star (R x.val * star (R (x + t.1).val))).re := by
      simpa only [hRval] using hcorr t ht
    obtain ⟨branch, a, len, hlen, hN, hshort, hinterval, hvolume⟩ :=
      exists_cyclic_derivative_integer_interval_re w R t.1 (Real.exp_pos (-q)) hw
        (fun n => M.norm_eval i _) hc
    exact ⟨branch, a, len, hlen, hN, hshort, hsmall.trans hinterval, hsmall.trans hvolume⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_derivative_correlation_mul_addChar {G : Type*} [AddCommGroup G] [Fintype G]
    (f u : G → ℂ) (χ : AddChar G ℂ) (h : G) :
    ‖finiteCorrelation Finset.univ f (multiplicativeDerivative (fun x => u x * χ x) h)‖ =
      ‖finiteCorrelation Finset.univ f (multiplicativeDerivative u h)‖ := by
  have hcancel (x : G) : χ x * star (χ x) = 1 := by
    change χ x * (starRingEnd ℂ) (χ x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, AddChar.norm_apply]
    norm_num
  have hder (x : G) : multiplicativeDerivative (fun y => u y * χ y) h x =
      star (χ h) * multiplicativeDerivative u h x := by
    simp only [multiplicativeDerivative, AddChar.map_add_eq_mul, star_mul]
    calc
      _ = (χ x * star (χ x)) * (star (χ h) * (u x * star (u (x + h)))) := by ring
      _ = _ := by rw [hcancel, one_mul]
  have heq : finiteCorrelation Finset.univ f (multiplicativeDerivative (fun x => u x * χ x) h) =
      χ h * finiteCorrelation Finset.univ f (multiplicativeDerivative u h) := by
    unfold finiteCorrelation
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    rw [hder, star_mul, star_star]
    ring
  rw [heq, norm_mul, AddChar.norm_apply, one_mul]

theorem exists_cubic_exchanged_correlations :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, t.2 ∈ H ∧ Real.exp (-((p + C) ^ C)) ≤
                ‖finiteCorrelation Finset.univ (multiplicativeDerivative (multiplicativeDerivative f t.1) t.2)
                  (multiplicativeDerivative (fun n => M.evalCyclic N i (correlationInput t.2 n)) t.1)‖ := by
  obtain ⟨A, _, hfixed⟩ := exists_cubic_fixed_fourier_correlation
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  classical
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 3 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, χ, hcorr⟩ :=
    hfixed hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  let g (h n : ZMod N) := if h ∈ H then M.evalCyclic N i (correlationInput h n) * χ h n else 0
  have hg (h n : ZMod N) : ‖g h n‖ ≤ 1 := by
    by_cases hh : h ∈ H
    · simp only [g, ite_eq_left hh, norm_mul, AddChar.norm_apply, mul_one]
      exact M.norm_eval i _
    · simp only [g, ite_eq_right hh, norm_zero, zero_le_one]
  have hzero (h : ZMod N) (hh : h ∉ H) (n : ZMod N) : g h n = 0 := by
    simp only [g, ite_eq_right hh]
  have hc (h : ZMod N) (hh : h ∈ H) : Real.exp (-q) ≤
      ‖finiteCorrelation Finset.univ (multiplicativeDerivative f h) (g h)‖ := by
    simpa only [g, finiteCorrelation, finiteFourierCoeff, ite_eq_left hh, star_mul,
      mul_assoc, mul_comm, mul_left_comm] using hcorr h hh
  obtain ⟨Q, hQ, hQsize, hQcorr⟩ := exists_many_exchanged_derivative_correlations f g H hf hg hzero
    (Real.exp_pos (-q)) (Real.exp_pos (-q)) (by simpa only [ZMod.card] using hdense) hc
  have hprod : Real.exp (-q) * Real.exp (-q) ^ 2 = Real.exp (-(3 * q)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
    ring
  have hsmall : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-q) * Real.exp (-q) ^ 2 / 2 := by
    rw [hprod]
    exact (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -(3 * q) - 1)).trans
      (exp_sub_one_le_half_exp (-(3 * q)))
  refine ⟨H, hH, ?_, M.mono hqC, i, χ, ?_, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · have hsize : Real.exp (-q) * Real.exp (-q) ^ 2 / 2 * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) := by
      simpa only [ZMod.card] using hQsize
    exact (mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)).trans hsize
  · intro t ht
    obtain ⟨hh, hlarge⟩ := hQcorr t ht
    refine ⟨hh, ?_⟩
    have hn := (hsmall.trans hlarge).trans (Complex.re_le_norm _)
    have heq : g t.2 = fun n => M.evalCyclic N i (correlationInput t.2 n) * χ t.2 n := by
      funext n
      simp only [g, ite_eq_left hh]
    rw [heq, norm_derivative_correlation_mul_addChar] at hn
    exact hn

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cubic_exchanged_intervals :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
          ∃ i : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ∧
            ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
              Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
              ∀ t ∈ Q, t.2 ∈ H ∧ ∃ (branch : Bool) (a len : ℕ),
                0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
                Real.exp (-((p + C) ^ C)) ≤
                  ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                    multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 (n : ZMod N) *
                      star (M.eval i (correlationInput (t.2.val : ℤ) n) *
                        star (M.eval i (correlationInput (t.2.val : ℤ)
                          (n + cyclicBranchOffset t.1 branch))))‖ ∧
                Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N := by
  obtain ⟨A, _, hexchange⟩ := exists_cubic_exchanged_correlations
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + 5)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + A) ^ A
  have htotal : q + 5 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have h20 : (20 : ℝ) ≤ Real.exp 5 :=
    (by norm_num : (20 : ℝ) ≤ 2 ^ 5).trans (two_pow_le_exp_of_le 5 le_rfl)
  have hsmall : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-q) / 20 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 20)).mpr
    calc
      _ ≤ Real.exp (-((p + C) ^ C)) * Real.exp 5 :=
        mul_le_mul_of_nonneg_left h20 (Real.exp_nonneg _)
      _ = Real.exp (-((p + C) ^ C) + 5) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨H, hH, hdense, M, i, χ, hcorr, Q, hQ, hQdense, hQcorr⟩ :=
    hexchange hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  refine ⟨H, hH, ?_, M.mono hqC, i, χ, ?_, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (sq_nonneg _)).trans hQdense
  · intro t ht
    obtain ⟨htH, htcor⟩ := hQcorr t ht
    let R (n : ℤ) := M.eval i (correlationInput (t.2.val : ℤ) n)
    let w (x : ZMod N) := multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 x
    have hRval (x : ZMod N) : R (x.val : ℤ) = M.evalCyclic N i (correlationInput t.2 x) := by
      change M.eval i (correlationInput (t.2.val : ℤ) (x.val : ℤ)) =
        M.eval i (fun j => ((correlationInput t.2 x j).val : ℤ))
      apply congrArg (M.eval i)
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    have hw (x : ZMod N) : ‖w x‖ ≤ 1 :=
      multiplicativeDerivative_norm_le_one _ (multiplicativeDerivative_norm_le_one f hf t.1) t.2 x
    have hc : Real.exp (-q) ≤
        ‖𝔼 x : ZMod N, w x * star (R x.val * star (R (x + t.1).val))‖ := by
      simpa only [hRval, w, finiteCorrelation, multiplicativeDerivative] using htcor
    obtain ⟨branch, a, len, hlen, hlenN, hshort, hinterval, hvolume⟩ :=
      exists_cyclic_derivative_integer_interval w R t.1 (Real.exp_pos (-q)) hw
        (fun n => M.norm_eval i _) hc
    exact ⟨htH, branch, a, len, hlen, hlenN, hshort, hsmall.trans hinterval, hsmall.trans hvolume⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMixedCorrelation

theorem exists_full_difference_correlation (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ i : Fin M.mixed.outputDim,
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ u ∈ Q, u.1 0 ∈ M.shifts ∧ Real.exp (-((p + C) ^ C)) ≤
          ‖finiteCorrelation Finset.univ
            (cubeProduct f (u.2 :: List.ofFn u.1))
            (cubeProduct (fun x => M.mixed.evalCyclic N i (correlationInput (u.1 0) x))
              (u.2 :: List.ofFn (Fin.tail u.1)))‖ := by
  obtain ⟨a, _, hfourier⟩ := exists_cube_residual_fourier_profiles d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  classical
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 3 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨i, H, _hH, hdense, χ, hcorr⟩ := hfourier hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  let F (u : Fin (d + 1) → ZMod N) := cubeProduct f (List.ofFn u)
  let V (u : Fin (d + 1) → ZMod N) :=
    cubeProduct (fun x => M.mixed.evalCyclic N i (correlationInput (u 0) x))
      (List.ofFn (Fin.tail u))
  let G (u : Fin (d + 1) → ZMod N) (x : ZMod N) := V u x * χ u x
  have hF (u : Fin (d + 1) → ZMod N) (x : ZMod N) : ‖F u x‖ ≤ 1 :=
    cubeProduct_norm_le_one f hf _ x
  have hV (u : Fin (d + 1) → ZMod N) (x : ZMod N) : ‖V u x‖ ≤ 1 :=
    cubeProduct_norm_le_one _ (fun _ => M.mixed.norm_eval i _) _ x
  have hG (u : Fin (d + 1) → ZMod N) (x : ZMod N) : ‖G u x‖ ≤ 1 := by
    dsimp only [G]
    rw [norm_mul, AddChar.norm_apply, mul_one]
    exact hV u x
  have hc (u : Fin (d + 1) → ZMod N) (hu : u ∈ H) :
      Real.exp (-q) ≤ ‖finiteCorrelation Finset.univ (F u) (G u)‖ := by
    have heq (x : ZMod N) : nativeMixedCubeResidual f M.mixed i u x * star (χ u x) =
        F u x * star (G u x) := by
      rw [nativeMixedCubeResidual_eq]
      dsimp only [F, G, V]
      rw [star_mul]
      ring
    simpa only [finiteFourierCoeff, finiteCorrelation, heq] using (hcorr u hu).2
  obtain ⟨Q, hQ, hQsize, hQcorr⟩ := exists_many_family_derivative_correlations F G H hF hG
    (Real.exp_pos (-q)) (Real.exp_pos (-q))
    (by simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow] using hdense) hc
  have hprod : Real.exp (-q) * Real.exp (-q) ^ 2 = Real.exp (-(3 * q)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsmall : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-q) * Real.exp (-q) ^ 2 / 2 := by
    rw [hprod]
    exact (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -(3 * q) - 1)).trans
      (exp_sub_one_le_half_exp (-(3 * q)))
  refine ⟨i, Q, hQ, ?_, ?_⟩
  · have hsize : Real.exp (-q) * Real.exp (-q) ^ 2 / 2 * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) := by
      convert hQsize using 1
      simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
      simp only [pow_succ]
      ring
    exact (mul_le_mul_of_nonneg_right hsmall (pow_nonneg (Nat.cast_nonneg N) _)).trans hsize
  · intro u hu
    obtain ⟨hbase, hder⟩ := hQcorr u hu
    refine ⟨(hcorr u.1 hbase).1, ?_⟩
    have h := hsmall.trans hder
    change Real.exp (-((p + C) ^ C)) ≤
      ‖finiteCorrelation Finset.univ (multiplicativeDerivative (F u.1) u.2)
        (multiplicativeDerivative (fun x => V u.1 x * χ u.1 x) u.2)‖ at h
    rw [norm_derivative_correlation_mul_addChar] at h
    have hFder : multiplicativeDerivative (F u.1) u.2 =
        cubeProduct f (u.2 :: List.ofFn u.1) := by
      funext x
      exact (cubeProduct_cons f u.2 (List.ofFn u.1) x).symm
    have hVder : multiplicativeDerivative (V u.1) u.2 =
        cubeProduct (fun x => M.mixed.evalCyclic N i (correlationInput (u.1 0) x))
          (u.2 :: List.ofFn (Fin.tail u.1)) := by
      funext x
      exact (cubeProduct_cons _ u.2 (List.ofFn (Fin.tail u.1)) x).symm
    rw [hFder, hVder] at h
    exact h

end NativeMixedCorrelation

theorem exists_mixed_full_differences_from_inverse (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ i : Fin M.mixed.outputDim,
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ u ∈ Q, u.1 0 ∈ M.shifts ∧ Real.exp (-((p + C) ^ C)) ≤
          ‖finiteCorrelation Finset.univ
            (cubeProduct f (u.2 :: List.ofFn u.1))
            (cubeProduct (fun x => M.mixed.evalCyclic N i (correlationInput (u.1 0) x))
              (u.2 :: List.ofFn (Fin.tail u.1)))‖ := by
  obtain ⟨a, _, hmixed⟩ := exists_native_mixed_from_inverse (by omega : 2 ≤ d + 2) hI
  obtain ⟨b, _, hdifference⟩ := NativeMixedCorrelation.exists_full_difference_correlation d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsum : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨M⟩ := hmixed hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  obtain ⟨i, Q, hQ, hdense, hcorr⟩ := hdifference hq ((Real.exp_le_exp.mpr hrC).trans hN) f hf M
  refine ⟨q, hq, hqC, M, i, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hrC))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro u hu
    exact ⟨(hcorr u hu).1, (Real.exp_le_exp.mpr (neg_le_neg hrC)).trans (hcorr u hu).2⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def mixedDifferenceShifts {d N : ℕ} (t : (Fin (d + 1) → ZMod N) × ZMod N) :
    Fin (d + 1) → ZMod N := Fin.cons t.2 (Fin.tail t.1)

def mixedDifferencePoint {d N : ℕ} (t : (Fin (d + 1) → ZMod N) × ZMod N) (n : ℤ) :
    Fin (d + 3) → ℤ :=
  Fin.cons ((t.1 0).val : ℤ) (Fin.cons n (fun j => ((mixedDifferenceShifts t j).val : ℤ)))

namespace NativeMixedCorrelation

theorem exists_cube_carry_intervals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ i : Fin M.mixed.outputDim,
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧
          ∃ (b : (Fin (d + 1) → Bool) → Fin (d + 2)) (a len : ℕ),
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
                  star (M.mixed.mixedCubeWithShift (cubeCarryShift (d + 1) N b)
                    (fun _ => i) (mixedDifferencePoint t n))‖ := by
  obtain ⟨A, _, hdifference⟩ := exists_full_difference_correlation d
  let L : ℕ := 2 * (2 ^ (d + 1) + 8)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + Polynomial.C L)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  let q := (p + A) ^ A
  have htotal : q + L ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    linarith
  have hLpos : (0 : ℝ) < L := by dsimp [L]; positivity
  have hLexp : (L : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp (L : ℝ)]
  have hsmall : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-q) / (2 * ((2 : ℝ) ^ (d + 1) + 8)) := by
    have hden : (2 * ((2 : ℝ) ^ (d + 1) + 8)) = L := by simp [L]
    rw [hden]
    apply (le_div_iff₀ hLpos).mpr
    calc
      _ ≤ Real.exp (-((p + C) ^ C)) * Real.exp L :=
        mul_le_mul_of_nonneg_left hLexp (Real.exp_nonneg _)
      _ = Real.exp (-((p + C) ^ C) + L) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨i, Q, hQ, hdense, hcorr⟩ := hdifference hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  refine ⟨i, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    refine ⟨(hcorr t ht).1, ?_⟩
    let R (z : ℤ) := M.mixed.eval i (correlationInput ((t.1 0).val : ℤ) z)
    let g := cubeProduct f (t.2 :: List.ofFn t.1)
    have hg : ∀ x, ‖g x‖ ≤ 1 := cubeProduct_norm_le_one f hf _
    have hR : (fun n : ZMod N => R n.val) =
        (fun x => M.mixed.evalCyclic N i (correlationInput (t.1 0) x)) := by
      funext x
      apply congrArg (M.mixed.eval i)
      funext j
      fin_cases j <;> rfl
    have hc : Real.exp (-q) ≤ ‖finiteCorrelation Finset.univ g
        (cubeProduct (fun n : ZMod N => R n.val) (List.ofFn (mixedDifferenceShifts t)))‖ := by
      rw [hR]
      simpa only [mixedDifferenceShifts, List.ofFn_cons] using (hcorr t ht).2
    obtain ⟨b, a, len, hlen, hend, hshort, hcor, hvol⟩ :=
      exists_cyclic_cube_product_interval g R (mixedDifferenceShifts t) (Real.exp_pos (-q))
        hg (fun _ => M.mixed.norm_eval i _) hc
    refine ⟨b, a, len, hlen, hend, hshort, hsmall.trans hvol, ?_⟩
    simpa only [finiteCorrelation, mixedDifferencePoint, M.mixed.mixedCubeWithShift_diagonal]
      using hsmall.trans hcor

end NativeMixedCorrelation
end Erdos3

end

section

namespace Erdos3.NativeMixedCorrelation

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_cube_unwrapped_intervals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∀ M : NativeMixedCorrelation (d + 2) N p f,
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ E : ∀ b : (Fin (d + 1) → Bool) → Fin (d + 2),
        NativeIntegerVectorEquivalence (d + 2) r
          (M.mixed.mixedCubeWithShift (cubeCarryShift (d + 1) N b))
          (M.mixed.mixedCubeWithShift 0),
      ∃ i : Fin M.mixed.outputDim,
      ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧
          ∃ (b : (Fin (d + 1) → Bool) → Fin (d + 2)) (a len : ℕ),
            0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
            Real.exp (-((p + C) ^ C)) ≤ (len : ℝ) / N ∧
            ∃ v : (Fin (d + 1) → Bool) → Fin M.mixed.outputDim,
            ∃ l : Fin ((E b).selectedExpansion (fun _ => i) v).count,
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
                  cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
                    star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n)) *
                    star ((((E b).selectedExpansion (fun _ => i) v).test l).eval (mixedDifferencePoint t n))‖ := by
  obtain ⟨A, _, hinterval⟩ := exists_cube_carry_intervals d
  obtain ⟨B, _, htranslate⟩ := NativeMultidegreeNilcharacter.exists_mixed_cube_translation (d + 2) (d + 1)
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  let R := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + 2 * R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf M
  let q := (p + A) ^ A
  let r := (p + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + 2 * r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨i, Q, hQ, hdense, hcorr⟩ := hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  let E (b : (Fin (d + 1) → Bool) → Fin (d + 2)) := htranslate M.mixed (cubeCarryShift (d + 1) N b)
  refine ⟨r, hr, hrC, E, i, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    obtain ⟨hshift, b, a, len, hlen, hend, hshort, hvol, hcor⟩ := hcorr t ht
    obtain ⟨v, l, hc⟩ := (E b).transfer_sample_correlation
      (Finset.Ico (a : ℤ) (a + len)) (mixedDifferencePoint t) (fun _ => i)
      (fun n => cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N))
      (fun n _ => M.mixed.mixedCubeWithShift_unit 0 _) hcor
    exact ⟨hshift, b, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol,
      v, l, (Real.exp_le_exp.mpr (neg_le_neg htotal)).trans hc⟩

end Erdos3.NativeMixedCorrelation

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

def HasFixedTargetCubeIntervals {J : Type*} [Fintype J] {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin 2 → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ r u : ℝ, 0 ≤ r ∧ r ≤ q ∧ 0 ≤ u ∧ u ≤ q ∧
    ∃ E : ∀ b : (Fin (d + 1) → Bool) → Fin (d + 2),
      NativeIntegerVectorEquivalence (d + 2) r
        (M.mixed.mixedCubeWithShift (cubeCarryShift (d + 1) N b)) (M.mixed.mixedCubeWithShift 0),
    ∃ F : NativeIntegerVectorEquivalence (d + 2) u (M.mixed.mixedCubeWithShift 0)
      (mixedCubeObservable (d := d + 1) η),
    ∃ (i : Fin M.mixed.outputDim) (b : (Fin (d + 1) → Bool) → Fin (d + 2))
      (v : (Fin (d + 1) → Bool) → Fin M.mixed.outputDim)
      (l : Fin ((E b).selectedExpansion (fun _ => i) v).count),
    ∃ (w : (Fin (d + 1) → Bool) → J) (z : Fin (F.selectedExpansion v w).count),
    ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
      Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
        0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
              star (mixedCubeObservable η w (mixedDifferencePoint t n)) *
              star ((((E b).selectedExpansion (fun _ => i) v).test l).eval (mixedDifferencePoint t n)) *
              star (((F.selectedExpansion v w).test z).eval (mixedDifferencePoint t n))‖

theorem HasFixedTargetCubeIntervals.mono {J : Type*} [Fintype J] {d N : ℕ} [NeZero N]
    {p q q' : ℝ} {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin 2 → ℤ) → ℂ} (H : HasFixedTargetCubeIntervals f M η q) (hqq' : q ≤ q') :
    HasFixedTargetCubeIntervals f M η q' := by
  obtain ⟨r, u, hr, hrq, hu, huq, E, F, i, b, v, l, w, z, Q, hQ, hdense, hcorr⟩ := H
  refine ⟨r, u, hr, hrq.trans hqq', hu, huq.trans hqq', E, F, i, b, v, l, w, z, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqq'))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hcorr t ht
    exact ⟨hs, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hc⟩

end Erdos3

end

section

namespace Erdos3.NativeMixedCorrelation

open scoped BigOperators TensorProduct

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_fixed_target_cube_intervals (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      ∀ (M : NativeMixedCorrelation (d + 2) N p f) (η : J → (Fin 2 → ℤ) → ℂ),
      (∀ x, ∑ j, ‖η j x‖ ^ 2 = 1) → NativeIntegerVectorEquivalence (d + 2) p M.mixed.eval η →
      HasFixedTargetCubeIntervals f M η ((p + C) ^ C) := by
  obtain ⟨A, _, hinterval⟩ := exists_cube_unwrapped_intervals d
  obtain ⟨B, _, hcube⟩ := NativeIntegerVectorEquivalence.exists_mixed_cube_budget (d + 1)
  let L : ℕ := (d + 2) ^ (2 ^ (d + 1))
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  let U := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * P + 2 * U + Polynomial.C L)
  refine ⟨C, hC, ?_⟩
  intro J _ N _ p hp hN f hf M η hη Ediag
  classical
  let q := (p + A) ^ A
  let u := (p + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have htotal : 3 * q + 2 * u + L ≤ (p + C) ^ C := by
    simpa [X, P, U, q, u, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by linarith
  have htransfer : q + 2 * u ≤ (p + C) ^ C := by linarith
  obtain ⟨r, hr, hrq, E, i, Q, hQ, hdense, hcorr⟩ :=
    hinterval hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf M
  have F : NativeIntegerVectorEquivalence (d + 2) u (M.mixed.mixedCubeWithShift 0)
      (mixedCubeObservable (d := d + 1) η) := by
    rw [M.mixed.mixedCubeWithShift_zero_eq]
    exact hcube hp Ediag
  let K := Σ b : (Fin (d + 1) → Bool) → Fin (d + 2),
    Σ v : (Fin (d + 1) → Bool) → Fin M.mixed.outputDim,
      Fin ((E b).selectedExpansion (fun _ => i) v).count ×
        (Σ w : (Fin (d + 1) → Bool) → J, Fin (F.selectedExpansion v w).count)
  let R (t : (Fin (d + 1) → ZMod N) × ZMod N) (_ : Unit) (c : K) : Prop :=
    t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
      0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-(q + 2 * u)) ≤
        ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
          cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
            star (mixedCubeObservable η c.2.2.2.1 (mixedDifferencePoint t n)) *
            star ((((E c.1).selectedExpansion (fun _ => i) c.2.1).test c.2.2.1).eval (mixedDifferencePoint t n)) *
            star (((F.selectedExpansion c.2.1 c.2.2.2.1).test c.2.2.2.2).eval (mixedDifferencePoint t n))‖
  have hchoice : ∀ t ∈ Q, ∀ j, ∃ c, R t j c := by
    intro t ht _
    obtain ⟨hshift, b, a, len, hlen, hend, hshort, hvol, v, l, hcor⟩ := hcorr t ht
    let D (n : ℤ) := cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N)
    let T (n : ℤ) := (((E b).selectedExpansion (fun _ => i) v).test l).eval (mixedDifferencePoint t n)
    have hc : Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        (D n * star (T n)) * star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n))‖ := by
      have hswap (n : ℤ) : D n * star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n)) * star (T n) =
          (D n * star (T n)) * star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n)) :=
        mul_right_comm _ _ _
      change Real.exp (-q) ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
        D n * star (M.mixed.mixedCubeWithShift 0 v (mixedDifferencePoint t n)) * star (T n)‖ at hcor
      simpa only [hswap] using hcor
    obtain ⟨w, z, hw⟩ := F.transfer_sample_correlation (Finset.Ico (a : ℤ) (a + len))
      (mixedDifferencePoint t) v (fun n => D n * star (T n))
      (fun n _ => mixedCubeObservable_unit η hη _) hc
    have horder (n : ℤ) :
        (D n * star (T n)) * star (mixedCubeObservable η w (mixedDifferencePoint t n)) *
          star (((F.selectedExpansion v w).test z).eval (mixedDifferencePoint t n)) =
        D n * star (mixedCubeObservable η w (mixedDifferencePoint t n)) * star (T n) *
          star (((F.selectedExpansion v w).test z).eval (mixedDifferencePoint t n)) :=
      congrArg (fun c : ℂ => c * star (((F.selectedExpansion v w).test z).eval (mixedDifferencePoint t n)))
        (mul_right_comm _ _ _)
    simp only [horder] at hw
    exact ⟨⟨b, v, l, w, z⟩, hshift, a, len, hlen, hend, hshort, hvol, hw⟩
  have hinner (b : (Fin (d + 1) → Bool) → Fin (d + 2)) :=
    (E b).selectedChainedChoice_card_bound F (fun _ => i)
  have hcount : (Fintype.card K : ℝ) ≤ Real.exp (2 * q + 2 * u + L) := by
    change (Fintype.card (Σ b : (Fin (d + 1) → Bool) → Fin (d + 2),
      Σ v : (Fin (d + 1) → Bool) → Fin M.mixed.outputDim,
        Fin ((E b).selectedExpansion (fun _ => i) v).count ×
          (Σ w : (Fin (d + 1) → Bool) → J, Fin (F.selectedExpansion v w).count)) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _b : (Fin (d + 1) → Bool) → Fin (d + 2), Real.exp (2 * r + 2 * u) :=
        Finset.sum_le_sum (fun b _ => hinner b)
      _ = (L : ℝ) * Real.exp (2 * r + 2 * u) := by simp [L]
      _ ≤ Real.exp L * Real.exp (2 * r + 2 * u) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (L : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (L + (2 * r + 2 * u)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨c, S, _, hS, hSdense, hfixed⟩ := exists_large_fixed_choices Q hQ R hchoice hcount
  have hsize : Real.exp (-(2 * q + 2 * u + L)) * (Q.card : ℝ) ≤ (S.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hSdense
  refine ⟨r, u, hr, hrq.trans hqC, hu, huC, E, F, i, (c ()).1, (c ()).2.1,
    (c ()).2.2.1, (c ()).2.2.2.1, (c ()).2.2.2.2, S, hS, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (-(3 * q + 2 * u + L)) * (N : ℝ) ^ (d + 2) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg htotal)) (by positivity)
      _ = Real.exp (-(2 * q + 2 * u + L)) * (Real.exp (-q) * (N : ℝ) ^ (d + 2)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(2 * q + 2 * u + L)) * (Q.card : ℝ) :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hsize
  · intro t ht
    obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hfixed t ht ()
    exact ⟨hs, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg htransfer)).trans hc⟩

end Erdos3.NativeMixedCorrelation

end

section

namespace Erdos3

open scoped BigOperators

def HasWeightedTargetCubeIntervals {J : Type*} [Fintype J] {d N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMixedCorrelation (d + 2) N p f)
    (η : J → (Fin 2 → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (w : (Fin (d + 1) → Bool) → J) (A : Fin (d + 3) → (Fin (d + 3) → ℤ) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    ∃ Q : Finset ((Fin (d + 1) → ZMod N) × ZMod N), Q.Nonempty ∧
      Real.exp (-q) * (N : ℝ) ^ (d + 2) ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, t.1 0 ∈ M.shifts ∧ ∃ a len : ℕ,
        0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
        Real.exp (-q) ≤ (len : ℝ) / N ∧ Real.exp (-q) ≤
          ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len),
            (cubeProduct f (t.2 :: List.ofFn t.1) (n : ZMod N) *
              star (mixedCubeObservable η w (mixedDifferencePoint t n))) *
              ∏ i, A i (mixedDifferencePoint t n)‖

theorem HasWeightedTargetCubeIntervals.mono {J : Type*} [Fintype J] {d N : ℕ} [NeZero N]
    {p q q' : ℝ} {f : ZMod N → ℂ} {M : NativeMixedCorrelation (d + 2) N p f}
    {η : J → (Fin 2 → ℤ) → ℂ} (H : HasWeightedTargetCubeIntervals f M η q) (hqq' : q ≤ q') :
    HasWeightedTargetCubeIntervals f M η q' := by
  obtain ⟨w, A, hA, hAi, Q, hQ, hdense, hcorr⟩ := H
  refine ⟨w, A, hA, hAi, Q, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqq'))
      (pow_nonneg (Nat.cast_nonneg N) _)).trans hdense
  · intro t ht
    obtain ⟨hs, a, len, hlen, hend, hshort, hvol, hc⟩ := hcorr t ht
    exact ⟨hs, a, len, hlen, hend, hshort,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hvol,
      (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hc⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_retained_target_cube_intervals (d : ℕ) {A : ℕ}
    (hI : CyclicNativeInverse (d + 2) A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (d + 4) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation (d + 2) N q f,
      ∃ W : NativeMultidegreeNilcharacter
        (fun _ : ReplicatedIndex (mixedCorrelationDegree (d + 2)) => 1) q,
        W.dim ≤ 2 ^ (d + 3) * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree (d + 2))) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree (d + 2)) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
          (fun k x => W.eval k (fun j => x j.1)) ∧
        HasFixedTargetCubeIntervals f M (fun k x => W.eval k (fun j => x j.1)) ((p + C) ^ C) := by
  obtain ⟨a, _, hretained⟩ := exists_retained_inverse_intervals (by omega : 2 ≤ d + 2) hI
  obtain ⟨b, _, hfixed⟩ := NativeMixedCorrelation.exists_fixed_target_cube_intervals d
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  let R := (P + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + R)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + a) ^ a
  let r := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : q + r ≤ (p + C) ^ C := by
    simpa [X, P, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  obtain ⟨q₀, hq₀, hq₀q, V, r₀, hr₀, hr₀q, B, M, hshifts, hdimension, E⟩ :=
    hretained hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  let W := B.mixed.mono hr₀q
  have hdiag : NativeIntegerVectorEquivalence (d + 2) q M.mixed.eval
      (fun k x => W.eval k (fun j => x j.1)) := E
  have H := hfixed hq ((Real.exp_le_exp.mpr hrC).trans hN) f hf M
    (fun k x => W.eval k (fun j => x j.1)) (fun x => W.unit_eval _) hdiag
  have hdim : W.dim ≤ 2 ^ (d + 3) * M.mixed.dim := by
    change B.mixed.dim ≤ 2 ^ (d + 3) * M.mixed.dim
    rw [hdimension]
    exact B.mixed_dim
  exact ⟨q, hq, hqC, M, W, hdim, B.mixed_symmetric, hdiag, H.mono hrC⟩

end Erdos3

end

end OAI
