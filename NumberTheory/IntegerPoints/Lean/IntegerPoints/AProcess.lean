import IntegerPoints.ExponentialSums
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The A-process for exponent pairs, part I: Graham–Kolesnik Lemma 3.7

`f ∈ F(N, P+1, s, y, ε)` on `[a, b]`, `0 < h ≤ b - a`, `h < εN/(s+P+1)` ⇒
`f₁(x) = f(x) - f(x+h)` lies in `F(N, P, s+1, shy, 3ε)` on `[a, b-h]`.

This is Lemma 3.7 of Graham–Kolesnik, *Van der Corput's Method of Exponential
Sums*, §3.4, with the slightly stronger hypothesis `h < εN/(s+P+1)` (instead of
`2εN/(s+P)`): we bound `∫_x^{x+h} (x^{-q} - u^{-q}) du ≤ q x^{-q-1} h²` by the
mean value theorem instead of `½ q x^{-q-1} h²` by a double integral.

Proof.  With `D = f^{(p+2)}` and `A(u) = (-1)^{p+1} (s)_{p+1} y u^{-q}`,
`q = s + p + 1`, the class condition for `f` at index `p+1` gives
`|D - A| < ε (s)_{p+1} y u^{-q}` on `[a, b]`.  By the fundamental theorem of
calculus `f₁^{(p+1)}(x) = -∫_x^{x+h} D`, so
`f₁^{(p+1)}(x) - (-1)^p (s)_{p+1} y h x^{-q}
  = -∫_x^{x+h} (D - A) - (-1)^p (s)_{p+1} y (h x^{-q} - ∫_x^{x+h} u^{-q} du)`,
and `0 ≤ h x^{-q} - ∫_x^{x+h} u^{-q} du ≤ q x^{-q-1} h² < ε h x^{-q}`.
-/

open Real Finset intervalIntegral

namespace LeanProofs.IntegerPoints

namespace AP

/-- `(s)_{p+1} = s (s+1)_p`. -/
theorem poch_succ (s : ℝ) (p : ℕ) :
    ∏ i ∈ range (p + 1), (s + i) = s * ∏ i ∈ range p, ((s + 1) + i) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.prod_range_succ, ih, Finset.prod_range_succ]
    push_cast
    ring

theorem poch_pos {s : ℝ} (hs : 0 < s) (p : ℕ) : 0 < ∏ i ∈ range p, (s + i) :=
  Finset.prod_pos fun i _ => add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg i)

/-- For `0 < t ≤ u` and `q ≥ 0`: `t^{-q} - q t^{-q-1} (u - t) ≤ u^{-q}`. -/
theorem rpow_neg_lower {t u q : ℝ} (ht : 0 < t) (htu : t ≤ u) (hq : 0 ≤ q) :
    t ^ (-q) - q * t ^ (-q - 1) * (u - t) ≤ u ^ (-q) := by
  rcases eq_or_lt_of_le htu with h | h
  · subst h; simp
  have hcont : ContinuousOn (fun v : ℝ => v ^ (-q)) (Set.Icc t u) :=
    (continuousOn_id.rpow_const fun v hv => Or.inl (show v ≠ 0 by linarith [hv.1])).congr
      fun v _ => rfl
  have hdiff : DifferentiableOn ℝ (fun v : ℝ => v ^ (-q)) (Set.Ioo t u) := fun v hv =>
    ((hasDerivAt_rpow_const (Or.inl (by linarith [hv.1]))).differentiableAt).differentiableWithinAt
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope (fun v : ℝ => v ^ (-q)) h hcont hdiff
  have hcd : deriv (fun v : ℝ => v ^ (-q)) c = -q * c ^ (-q - 1) :=
    (hasDerivAt_rpow_const (Or.inl (by linarith [hc.1]))).deriv
  rw [hcd] at hc'
  have hslope : u ^ (-q) - t ^ (-q) = -q * c ^ (-q - 1) * (u - t) := by
    rw [hc', div_mul_cancel₀ _ (by linarith)]
  have hcle : c ^ (-q - 1) ≤ t ^ (-q - 1) :=
    Real.rpow_le_rpow_of_nonpos ht hc.1.le (by linarith)
  have hut : 0 ≤ u - t := by linarith
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcle hq) hut
  linarith

/-- **Graham–Kolesnik, Lemma 3.7** (variant).  If `f ∈ F(N, P+1, s, y, ε)` on `[a, b]`,
`0 < h ≤ b - a` and `h < εN/(s+P+1)`, then `x ↦ f(x) - f(x+h)` lies in
`F(N, P, s+1, shy, 3ε)` on `[a, b-h]`. -/
theorem lemma37 {N : ℝ} {P : ℕ} {s y ε a b h : ℝ} {f : ℝ → ℝ}
    (hs : 0 < s) (hy : 0 < y) (hε : 0 < ε)
    (hf : InGKClass N (P + 1) s y ε a b f) (hh0 : 0 < h) (hhb : h ≤ b - a)
    (hhN : h < ε * N / (s + P + 1)) :
    InGKClass N P (s + 1) (s * h * y) (3 * ε) a (b - h) (fun x => f x - f (x + h)) := by
  obtain ⟨hNa, hab, hb2N, hcd, hcond⟩ := hf
  have hN : 0 < N := by
    by_contra hN
    push Not at hN
    have : ε * N / (s + P + 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hε.le hN) (by positivity)
    linarith
  refine ⟨hNa, by linarith, by linarith, ?_, ?_⟩
  · have h1 : ContDiff ℝ P f := hcd.of_le (by exact_mod_cast Nat.le_succ P)
    have h2 : ContDiff ℝ P (fun x => f (x + h)) := h1.comp (contDiff_id.add contDiff_const)
    exact h1.sub h2
  intro p hp t ht
  obtain ⟨hat, htb⟩ := ht
  have ht0 : 0 < t := by linarith
  -- notation
  set q : ℝ := s + ((p + 1 : ℕ) : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; positivity
  have hexp : -s - ((p + 1 : ℕ) : ℝ) = -q := by rw [hq]; ring
  set c : ℝ := ∏ i ∈ range (p + 1), (s + i) with hc
  have hc0 : 0 < c := poch_pos hs (p + 1)
  set K0 : ℝ := (-1) ^ (p + 1) * c * y with hK0
  set D : ℝ → ℝ := iteratedDeriv (p + 1 + 1) f with hD
  set A : ℝ → ℝ := fun u => K0 * u ^ (-q) with hA
  -- the class condition for `f` at index `p + 1`
  have hDA : ∀ u ∈ Set.Icc a b, |D u - A u| < ε * c * y * u ^ (-q) := by
    intro u hu
    have := hcond (p + 1) (by omega) u hu
    rw [hexp] at this
    rw [hD, hA, hK0]
    simpa [mul_assoc] using this
  -- regularity
  have hp1 : ((p + 1 : ℕ) : WithTop ℕ∞) < ((P + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by omega : p + 1 < P + 1)
  have hp2 : ((p + 1 + 1 : ℕ) : WithTop ℕ∞) ≤ ((P + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (by omega : p + 1 + 1 ≤ P + 1)
  have hdiff : Differentiable ℝ (iteratedDeriv (p + 1) f) :=
    hcd.differentiable_iteratedDeriv (p + 1) hp1
  have hDc : Continuous D := hcd.continuous_iteratedDeriv (p + 1 + 1) hp2
  have hcf : ContDiff ℝ (p + 1) f := hcd.of_le (by exact_mod_cast (by omega : p + 1 ≤ P + 1))
  have hcg : ContDiff ℝ (p + 1) (fun x => f (x + h)) :=
    hcf.comp (contDiff_id.add contDiff_const)
  -- the `(p+1)`-st derivative of `f₁`
  have hder : iteratedDeriv (p + 1) (fun x => f x - f (x + h)) t =
      iteratedDeriv (p + 1) f t - iteratedDeriv (p + 1) f (t + h) := by
    have e : (fun x => f x - f (x + h)) = f - fun x => f (x + h) := rfl
    rw [e, iteratedDeriv_sub hcf.contDiffAt hcg.contDiffAt, iteratedDeriv_comp_add_const]
  -- fundamental theorem of calculus
  set J : ℝ := ∫ u in t..t + h, D u with hJ
  have hX : iteratedDeriv (p + 1) f t - iteratedDeriv (p + 1) f (t + h) = -J := by
    have := integral_eq_sub_of_hasDerivAt (f := iteratedDeriv (p + 1) f) (f' := D)
      (a := t) (b := t + h) (fun x _ => by
        rw [hD, iteratedDeriv_succ (n := p + 1)]
        exact (hdiff x).hasDerivAt) (hDc.intervalIntegrable _ _)
    rw [hJ, this]
    ring
  -- integrability of the pieces
  have hrp : IntervalIntegrable (fun u : ℝ => u ^ (-q)) MeasureTheory.volume t (t + h) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.rpow_const continuousOn_id
    intro v hv
    rw [Set.uIcc_of_le (by linarith)] at hv
    exact Or.inl (show v ≠ 0 by linarith [hv.1])
  have hAi : IntervalIntegrable A MeasureTheory.volume t (t + h) := by
    rw [hA]
    exact hrp.const_mul K0
  have hDi : IntervalIntegrable D MeasureTheory.volume t (t + h) := hDc.intervalIntegrable _ _
  set I : ℝ := ∫ u in t..t + h, u ^ (-q) with hI
  have hJsplit : J = (∫ u in t..t + h, (D u - A u)) + K0 * I := by
    rw [integral_sub hDi hAi, hA, integral_const_mul, hJ, hI]
    ring
  -- the error integral
  have h1 : |∫ u in t..t + h, (D u - A u)| ≤ ε * c * y * t ^ (-q) * h := by
    have := norm_integral_le_of_norm_le_const (a := t) (b := t + h)
      (f := fun u => D u - A u) (C := ε * c * y * t ^ (-q)) (fun u hu => by
        rw [Set.uIoc_of_le (by linarith)] at hu
        rw [Real.norm_eq_abs]
        have hu' : u ∈ Set.Icc a b := ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have hle : u ^ (-q) ≤ t ^ (-q) :=
          Real.rpow_le_rpow_of_nonpos ht0 hu.1.le (by linarith)
        have := hDA u hu'
        nlinarith [mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ ε * c * y)])
    rw [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hh0] at this
    exact this
  -- bounds for `I`
  have h2 : h * (t ^ (-q) - q * t ^ (-q - 1) * h) ≤ I := by
    have := integral_mono_on (a := t) (b := t + h) (by linarith)
      (intervalIntegrable_const (c := t ^ (-q) - q * t ^ (-q - 1) * h)) hrp (fun u hu => by
        have := rpow_neg_lower ht0 hu.1 hq0.le (u := u)
        have hut : u - t ≤ h := by linarith [hu.2]
        have : q * t ^ (-q - 1) * (u - t) ≤ q * t ^ (-q - 1) * h :=
          mul_le_mul_of_nonneg_left hut (by positivity)
        linarith)
    rw [integral_const, add_sub_cancel_left, smul_eq_mul] at this
    exact this
  have h3 : I ≤ h * t ^ (-q) := by
    have := integral_mono_on (a := t) (b := t + h) (by linarith) hrp
      (intervalIntegrable_const (c := t ^ (-q))) (fun u hu =>
        Real.rpow_le_rpow_of_nonpos ht0 hu.1 (by linarith))
    rw [integral_const, add_sub_cancel_left, smul_eq_mul] at this
    exact this
  -- the target, rewritten
  have hK : (-1) ^ p * (∏ i ∈ range p, ((s + 1) + i)) * (s * h * y) * t ^ (-(s + 1) - p) =
      (-1) ^ p * c * y * h * t ^ (-q) := by
    rw [hc, poch_succ, show (-(s + 1) - p : ℝ) = -q by rw [hq]; push_cast; ring]
    ring
  have hB : 3 * ε * (∏ i ∈ range p, ((s + 1) + i)) * (s * h * y) * t ^ (-(s + 1) - p) =
      3 * ε * (c * y * h * t ^ (-q)) := by
    rw [hc, poch_succ, show (-(s + 1) - p : ℝ) = -q by rw [hq]; push_cast; ring]
    ring
  rw [hder, hX, hK, hB]
  have hK0' : K0 = -((-1) ^ p * c * y) := by rw [hK0, pow_succ]; ring
  have hmain : -J - (-1) ^ p * c * y * h * t ^ (-q) =
      -(∫ u in t..t + h, (D u - A u)) - (-1) ^ p * c * y * (h * t ^ (-q) - I) := by
    rw [hJsplit, hK0']
    ring
  rw [hmain]
  have hBpos : 0 < c * y * h * t ^ (-q) := by positivity
  have hw : 0 ≤ h * t ^ (-q) - I := by linarith
  have hqh : q * h < ε * t := by
    have hq' : q ≤ s + P + 1 := by
      rw [hq]
      have : ((p + 1 : ℕ) : ℝ) ≤ P := by exact_mod_cast (by omega : p + 1 ≤ P)
      linarith
    have hsP : 0 < s + P + 1 := by positivity
    rw [lt_div_iff₀ hsP] at hhN
    calc q * h ≤ (s + P + 1) * h := mul_le_mul_of_nonneg_right hq' hh0.le
      _ = h * (s + P + 1) := mul_comm _ _
      _ < ε * N := hhN
      _ ≤ ε * t := mul_le_mul_of_nonneg_left (by linarith) hε.le
  have h4 : c * y * (h * t ^ (-q) - I) < ε * (c * y * h * t ^ (-q)) := by
    have hle : h * t ^ (-q) - I ≤ q * t ^ (-q - 1) * h ^ 2 := by nlinarith
    have e : t ^ (-q - 1) = t ^ (-q) / t := Real.rpow_sub_one ht0.ne' _
    calc c * y * (h * t ^ (-q) - I) ≤ c * y * (q * t ^ (-q - 1) * h ^ 2) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (c * y * h * t ^ (-q)) * (q * h / t) := by
          rw [e]
          first | (field_simp; done) | (field_simp; ring)
      _ < (c * y * h * t ^ (-q)) * ε :=
          mul_lt_mul_of_pos_left ((div_lt_iff₀ ht0).2 hqh) hBpos
      _ = ε * (c * y * h * t ^ (-q)) := by ring
  calc |-(∫ u in t..t + h, (D u - A u)) - (-1) ^ p * c * y * (h * t ^ (-q) - I)|
      ≤ |-(∫ u in t..t + h, (D u - A u))| + |(-1) ^ p * c * y * (h * t ^ (-q) - I)| :=
        abs_sub _ _
    _ = |∫ u in t..t + h, (D u - A u)| + c * y * (h * t ^ (-q) - I) := by
        rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_pos hc0, abs_of_pos hy, abs_of_nonneg hw]
    _ < 3 * ε * (c * y * h * t ^ (-q)) := by
        have : ε * c * y * t ^ (-q) * h = ε * (c * y * h * t ^ (-q)) := by ring
        rw [this] at h1
        linarith [mul_pos hε hBpos]

end AP

end LeanProofs.IntegerPoints
