import OAI.Combinatorics.Progressions.Lattices.AbsoluteCRTWindow
import OAI.Combinatorics.Progressions.Lattices.ScoredCRTWindowPatch

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_absolute_crt_patch {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
        (_hprime : ∀ j, (N j).Prime) (_hinj : Function.Injective N)
        (f : ((j : J) → ZMod (N j)) → ℝ) {alpha p : ℝ},
        0 < alpha → 2 ≤ p → Real.log (1 / alpha) ≤ p →
        (∀ j, Real.exp ((p + 2) ^ C) ≤ N j) →
        (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (𝔼 x, f x) = alpha →
        IntegerVectorAPFree (residueBoxIntegerPoint N '' Function.support f) k →
        ∃ d : ℕ, ∃ P : PolynomialPatch J (k - 2) d,
          (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
          Real.exp (-((p + 2) ^ C)) ≤
            (𝔼 x, (f x - (1 + xi) * alpha) * P.value (fun j => ((x j).val : ℝ))) := by
  obtain ⟨Csc, _, Cside, hCside, _, Cwindow, _, xi, hxi, hwindow⟩ :=
    exists_absolute_crt_window (J := J) k hk
  obtain ⟨A, _, hconvert⟩ := exists_scored_windowed_crt_patch.{0} (k - 2) (by omega)
  obtain ⟨B, _, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (((Polynomial.X + 2) ^ (max Csc Cwindow) + 2) ^ A)
  let C := max Cside B
  refine ⟨C, hCside.trans (le_max_left _ _), xi, hxi, ?_⟩
  intro N _ _ hprime hinj f alpha p halpha hp hlog hsize hf hmean hfree
  have hp0 : 0 ≤ p := by linarith
  have hbase : 1 ≤ p + 2 := by linarith
  have hside : (p + 2) ^ Cside ≤ (p + 2) ^ C :=
    pow_le_pow_right₀ hbase (le_max_left _ _)
  obtain ⟨T, w, hT, hw, hscore⟩ := hwindow N hprime hinj f halpha hp hlog
    (fun j => (Real.exp_le_exp.mpr hside).trans (hsize j)) hf hmean hfree
  let q := (p + 2) ^ (max Csc Cwindow)
  have hq : 0 ≤ q := pow_nonneg (by linarith) _
  have hsc : (p + 2) ^ Csc ≤ q := pow_le_pow_right₀ hbase (le_max_left _ _)
  have hwin : (p + 2) ^ Cwindow ≤ q := pow_le_pow_right₀ hbase (le_max_right _ _)
  let hN := distinct_prime_moduli_coprime N hprime hinj
  have hs : Real.exp (-q) ≤
      (𝔼 x, ((f x - (1 + xi) * alpha) * T ((ZMod.prodEquivPi N hN).symm x)) *
        w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))) := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hwin)).trans
    simpa only [RepresentativeWindow.crtPatch_value_residues] using hscore
  obtain ⟨d, P, hP, hscoreP⟩ := hconvert N hN T w (fun x => f x - (1 + xi) * alpha)
    hq (hT.mono le_rfl hsc) (hw.trans hwin) hs
  have hbound : (q + 2) ^ A ≤ (p + 2) ^ C := by
    apply le_trans _ (pow_le_pow_right₀ hbase (le_max_right _ _))
    simpa [q, Polynomial.eval₂_pow] using hbudget p hp0
  exact ⟨d, P, hP.trans hbound, (Real.exp_le_exp.mpr (neg_le_neg hbound)).trans hscoreP⟩

end Erdos3

end

end OAI
