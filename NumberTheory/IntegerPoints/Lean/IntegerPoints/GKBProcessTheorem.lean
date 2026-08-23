import IntegerPoints.ExponentPairHalf
import IntegerPoints.ExponentPairs
import IntegerPoints.GKBProcessMainBound
import IntegerPoints.GKBProcessRegimes
import IntegerPoints.GKLegendreExtension
import IntegerPoints.GKSec33Boundary

/-!
# Graham--Kolesnik Theorem 3.10: the B-process

This module assembles the quantitative B-process layers.  The proof first
removes the unique boundary pair with second coordinate `1 / 2`.  Away from
that boundary, the input class is intersected with the class used by the
proved pair `(1/2,1/2)`.  The resulting estimate is split into three regimes:

* `N < 1`, where the interval contains at most one summand;
* `N >= 1` and `L = y N^(-s) <= 1`, where the `(1/2,1/2)` estimate suffices;
* `N,L >= 1`, where Lemma 3.6, the global Legendre phase, and the dyadic
  inverse-phase bound give the B-transform.

All constants inherited from existential estimates are replaced by their
maximum with zero before they are multiplied by a nonnegative model.  Thus
the final argument does not silently assume that an existentially supplied
constant has a sign.
-/

open scoped BigOperators
open Real Finset Set

namespace LeanProofs.IntegerPoints

set_option maxHeartbeats 1600000 in
/-- **Graham--Kolesnik, Theorem 3.10**: the B-process sends an exponent pair
`(k,l)` to `(l-1/2,k+1/2)`. -/
theorem gk_theorem310_holds : gk_theorem310 := by
  intro k l hpair
  by_cases hlBoundary : l = 1 / 2
  · have hkBoundary : k = 1 / 2 :=
      gk_sec33_k_eq_half_of_l_eq_half_holds k (by
        simpa only [hlBoundary] using hpair)
    subst k
    subst l
    convert isExponentPair_zero_one using 1 <;> norm_num
  have hlStrict : 1 / 2 < l :=
    lt_of_le_of_ne hpair.2.2.1 (Ne.symm hlBoundary)
  refine ⟨by linarith [hpair.2.2.1], by linarith [hpair.2.2.2.1],
    by linarith [hpair.1], by linarith [hpair.2.1], ?_⟩
  intro s hs

  -- The B-process package uses the input pair at the inverse exponent.  We
  -- intersect its original class with one class for the proved half pair,
  -- which handles the small-dual-scale regime.
  let params : GKB.Parameters k l s := GKB.chooseParameters hpair hs
  obtain ⟨Phalf, epsHalf, ChalfRaw, hepsHalf, -, hhalfRaw⟩ :=
    isExponentPair_half_half.2.2.2.2 s hs
  let P : ℕ := max params.originalOrder Phalf
  let eps : ℝ := min params.originalError epsHalf
  have heps : 0 < eps := by
    exact lt_min params.originalError_pos hepsHalf
  have hepsLt : eps < 1 / 2 :=
    (min_le_left params.originalError epsHalf).trans_lt
      params.originalError_lt_half

  -- Select Lemma 3.6 once, since its geometric constants depend only on `s`.
  have hcurvature := GKB.curvatureConstants_pos hs
  obtain ⟨C36Raw, h36Raw⟩ := gk_lemma36_holds
    (GKB.curvatureLower s) (GKB.curvatureUpper s)
    (GKB.curvatureThird s) (GKB.curvatureFourth s)
    hcurvature.1 hcurvature.2.1 hcurvature.2.2.1 hcurvature.2.2.2

  let Chalf : ℝ := max ChalfRaw 0
  let C36 : ℝ := max C36Raw 0
  let Cmain : ℝ := GKB.mainBoundConstant params
  let delta : ℝ := l - 1 / 2
  let Clog : ℝ := Real.log 3 + delta⁻¹
  let Canalytic : ℝ := C36 * (Clog + 1) + 2 * Cmain
  let Cfinal : ℝ := 2 + Chalf + Canalytic
  have hChalf : 0 ≤ Chalf := le_max_right _ _
  have hC36 : 0 ≤ C36 := le_max_right _ _
  have hCmain : 0 ≤ Cmain := by
    dsimp only [Cmain]
    exact GKB.mainBoundConstant_nonneg params hs
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  have hClog : 0 < Clog := by
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hdeltaInv : 0 < delta⁻¹ := inv_pos.mpr hdelta
    dsimp only [Clog]
    exact add_pos hlog3 hdeltaInv
  have hCanalytic : 0 ≤ Canalytic := by
    dsimp only [Canalytic]
    positivity
  have hCfinal : 0 ≤ Cfinal := by
    dsimp only [Cfinal]
    positivity

  refine ⟨P, eps, Cfinal, heps, hepsLt, ?_⟩
  intro N y a b f hN hy hf
  have hPparams : params.originalOrder ≤ P := by
    dsimp only [P]
    exact le_max_left _ _
  have hPhalf : Phalf ≤ P := by
    dsimp only [P]
    exact le_max_right _ _
  have hepsParams : eps ≤ params.originalError := by
    dsimp only [eps]
    exact min_le_left _ _
  have hepsHalf' : eps ≤ epsHalf := by
    dsimp only [eps]
    exact min_le_right _ _
  have hfParams :
      InGKClass N params.originalOrder s y params.originalError a b f :=
    InGKClass.weaken_of_pos hN hs hy hPparams hepsParams hf
  have hfHalf : InGKClass N Phalf s y epsHalf a b f :=
    InGKClass.weaken_of_pos hN hs hy hPhalf hepsHalf' hf

  set L : ℝ := GKB.dualScale N s y with hLDef
  set X : ℝ :=
    L ^ (l - 1 / 2) * N ^ (k + 1 / 2) + L⁻¹ with hXDef
  have hL : 0 < L := by
    rw [hLDef]
    exact GKB.dualScale_pos hN hy
  have hscale : L = y * N ^ (-s) := by
    rw [hLDef]
    rfl
  have hinvScale : L⁻¹ = y⁻¹ * N ^ s := by
    rw [hLDef, GKB.inv_dualScale_eq hN]
  have hXtarget :
      X = (y * N ^ (-s)) ^ (l - 1 / 2) * N ^ (k + 1 / 2) +
        y⁻¹ * N ^ s := by
    rw [hXDef, hinvScale, hscale]
  have hX : 0 ≤ X := by
    rw [hXDef]
    positivity

  -- Each regime supplies a local constant bounded by `Cfinal`.
  suffices hlocal : ∃ c : ℝ, c ≤ Cfinal ∧
      ‖∑ n ∈ intRange a b, e (f n)‖ ≤ c * X by
    obtain ⟨c, hc, hbound⟩ := hlocal
    rw [← hXtarget]
    exact hbound.trans (mul_le_mul_of_nonneg_right hc hX)

  rcases lt_or_ge N 1 with hNone | hNone
  · refine ⟨2, ?_, ?_⟩
    · dsimp only [Cfinal]
      linarith [hChalf, hCanalytic]
    · exact GKB.norm_sum_intRange_e_le_two_mul_bRhs_of_lt_one
        hN hNone hL hf.2.2.1 hpair.2.1 hpair.2.2.1

  -- Normalize the half-pair constant before using its estimate.
  have hhalfRaw' := hhalfRaw N y a b f hN hy hfHalf
  have hhalfModel :
      0 ≤ (y * N ^ (-s)) ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) +
        y⁻¹ * N ^ s := by positivity
  have hhalf :
      ‖∑ n ∈ intRange a b, e (f n)‖ ≤
        Chalf * (L ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) + L⁻¹) := by
    have hnormalized := hhalfRaw'.trans
      (mul_le_mul_of_nonneg_right (le_max_left ChalfRaw 0) hhalfModel)
    rw [← hscale, ← hinvScale] at hnormalized
    exact hnormalized
  rcases le_or_gt L 1 with hLone | hLone
  · refine ⟨Chalf, ?_, ?_⟩
    · dsimp only [Cfinal]
      linarith [hCanalytic]
    · calc
        ‖∑ n ∈ intRange a b, e (f n)‖ ≤
            Chalf * (L ^ (1 / 2 : ℝ) * N ^ (1 / 2 : ℝ) + L⁻¹) := hhalf
        _ ≤ Chalf * X := by
          apply mul_le_mul_of_nonneg_left _ hChalf
          rw [hXDef]
          exact GKB.halfPairModel_le_bRhs_of_le_one
            hNone hL hLone hpair.1 hpair.2.2.2.1

  have hLone' : 1 ≤ L := hLone.le
  have hLoneScale : 1 ≤ GKB.dualScale N s y := by
    rw [← hLDef]
    exact hLone'
  rcases hfParams.2.1.eq_or_lt with hab | hab
  · subst b
    refine ⟨0, hCfinal, ?_⟩
    simp [intRange]

  -- Negative curvature gives globally defined inverse and Legendre data.
  have hPtwo : 2 ≤ params.originalOrder := by
    exact (by norm_num : 2 ≤ 4).trans params.four_le_originalOrder
  obtain ⟨x, phi, hphi, hx, hlegendre⟩ :=
    GKLegendre.exists_legendre_data hPtwo hab hfParams.2.2.2.1 (by
      intro t ht
      simpa only [GK34.iteratedDeriv_two] using
        GKB.second_derivative_neg hN hs hy params.four_le_originalOrder
          params.originalError_le_quarter hfParams t ht)

  let S : ℂ := ∑ n ∈ intRange a b, e (f n)
  let M : ℂ :=
    ∑ nu ∈ Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋,
      e (f (x (nu : ℝ)) - (nu : ℝ) * x (nu : ℝ) - 1 / 8) /
        ((Real.sqrt |iteratedDeriv 2 f (x (nu : ℝ))| : ℝ) : ℂ)

  obtain ⟨hF, hNa, hab', hb, hfFour, hsecond, hthird, hfourth⟩ :=
    GKB.lemma36_geometry hN hs hy params.four_le_originalOrder
      params.originalError_le_quarter hfParams
  have hxInt : ∀ nu : ℤ, deriv f b ≤ (nu : ℝ) →
      (nu : ℝ) ≤ deriv f a →
      x (nu : ℝ) ∈ Icc a b ∧ deriv f (x (nu : ℝ)) = (nu : ℝ) := by
    intro nu hnuLeft hnuRight
    exact hx (nu : ℝ) ⟨hnuLeft, hnuRight⟩
  have h36Raw' := h36Raw N (GKB.phaseScale N s y) a b f
    (fun nu : ℤ => x (nu : ℝ)) hN hF hNa hab' hb hfFour
      hsecond hthird hfourth hxInt
  rw [GKB.phaseScale_mul_inv hN, ← hLDef] at h36Raw'
  change ‖S - M‖ ≤ C36Raw *
    (Real.log (L + 2) + GKB.phaseScale N s y ^ (-(1 : ℝ) / 2) * N) at h36Raw'
  have hErrorModel :
      0 ≤ Real.log (L + 2) +
        GKB.phaseScale N s y ^ (-(1 : ℝ) / 2) * N := by
    apply add_nonneg
    · exact Real.log_nonneg (by linarith)
    · positivity
  have h36 : ‖S - M‖ ≤ C36 *
      (Real.log (L + 2) +
        GKB.phaseScale N s y ^ (-(1 : ℝ) / 2) * N) :=
    h36Raw'.trans
      (mul_le_mul_of_nonneg_right (le_max_left C36Raw 0) hErrorModel)

  have hmainRaw :=
    GKB.lemma36_mainTerm_le_two_mul_mainBoundConstant_mul_bMain
      params hNone hs hy hLoneScale hpair.1 hpair.2.2.1 hfParams hab
        hphi hx hlegendre
  rw [← hLDef] at hmainRaw
  change ‖M‖ ≤ (2 * Cmain) *
    (L ^ (l - 1 / 2) * N ^ (k + 1 / 2)) at hmainRaw
  have hmain : ‖M‖ ≤ (2 * Cmain) *
      (L ^ (l - 1 / 2) * N ^ (k + 1 / 2)) := hmainRaw

  -- The logarithm and the power error are both absorbed by the B main term.
  have hNpower : 1 ≤ N ^ (k + 1 / 2) :=
    Real.one_le_rpow hNone (by linarith [hpair.1])
  have hlogB : Real.log (L + 2) ≤
      Clog * (L ^ (l - 1 / 2) * N ^ (k + 1 / 2)) := by
    calc
      Real.log (L + 2) ≤ Clog * L ^ delta := by
        simpa only [Clog] using GKB.log_add_two_le_rpow hdelta hLone'
      _ ≤ Clog * (L ^ (l - 1 / 2) * N ^ (k + 1 / 2)) := by
        apply mul_le_mul_of_nonneg_left _ hClog.le
        dsimp only [delta]
        calc
          L ^ (l - 1 / 2) = L ^ (l - 1 / 2) * 1 := by ring
          _ ≤ L ^ (l - 1 / 2) * N ^ (k + 1 / 2) :=
            mul_le_mul_of_nonneg_left hNpower (by positivity)
  have hpowerError :
      GKB.phaseScale N s y ^ (-(1 : ℝ) / 2) * N ≤
        L ^ (l - 1 / 2) * N ^ (k + 1 / 2) := by
    rw [hLDef]
    exact GKB.phaseScale_neg_half_mul_le_bMain
      hNone hy hLoneScale hpair.1 hpair.2.2.1

  refine ⟨Canalytic, ?_, ?_⟩
  · dsimp only [Cfinal]
    linarith [hChalf]
  · change ‖S‖ ≤ Canalytic * X
    calc
      ‖S‖ = ‖(S - M) + M‖ := by congr 1; ring
      _ ≤ ‖S - M‖ + ‖M‖ := norm_add_le _ _
      _ ≤ C36 *
            (Real.log (L + 2) +
              GKB.phaseScale N s y ^ (-(1 : ℝ) / 2) * N) +
          (2 * Cmain) *
            (L ^ (l - 1 / 2) * N ^ (k + 1 / 2)) :=
        add_le_add h36 hmain
      _ ≤ C36 *
            (Clog * (L ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
              L ^ (l - 1 / 2) * N ^ (k + 1 / 2)) +
          (2 * Cmain) *
            (L ^ (l - 1 / 2) * N ^ (k + 1 / 2)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (add_le_add hlogB hpowerError) hC36)
          le_rfl
      _ = Canalytic *
          (L ^ (l - 1 / 2) * N ^ (k + 1 / 2)) := by
        dsimp only [Canalytic]
        ring
      _ ≤ Canalytic * X := by
        apply mul_le_mul_of_nonneg_left _ hCanalytic
        rw [hXDef]
        exact le_add_of_nonneg_right (inv_nonneg.mpr hL.le)

end LeanProofs.IntegerPoints
