import OAI.Combinatorics.Progressions.Dynamics.AllocatedFiniteIdealMaskBudget
import OAI.Combinatorics.Progressions.Sampling.AllocatedSlicedGridResourceBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

theorem allocatedAffineFactor_exp_bound {B Q Op Pper cutoff coord Qgrid Mp period r radius : ℝ}
    (axes gridaxes : ℕ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hOp : 0 ≤ Op) (hPper : 0 ≤ Pper)
    (ha : (axes : ℝ) ≤ B) (hg : (gridaxes : ℝ) ≤ B)
    (hc0 : 0 ≤ cutoff) (hcoord0 : 0 ≤ coord) (hgrid0 : 0 ≤ Qgrid) (hMp0 : 0 ≤ Mp)
    (hper0 : 0 ≤ period) (hc : cutoff ≤ Real.exp B) (hcoord : coord ≤ Real.exp B)
    (hQgrid : Qgrid ≤ Real.exp B) (hMp : Mp ≤ Real.exp Pper) (hper : period ≤ Real.exp Pper)
    (hr : 1 ≤ r) (hradius : 1 ≤ radius) :
    let Llong := (axes * cutoff / (2 * r)) * coord +
      max ((Real.exp (axes + 6 * Q + 12) + axes * cutoff / (2 * radius)) * coord * Mp) (4 * Mp)
    let Lgrid := max (gridaxes * Real.exp Op * Qgrid * coord * (Real.exp Op) ^ gridaxes)
      (4 * (Real.exp Op) ^ gridaxes)
    (Llong + Lgrid) * (period * (Real.exp Op) ^ gridaxes) ≤
      Real.exp (10 * B + 6 * Q + 2 * Pper + (2 * B + 1) * Op + 19) := by
  intro Llong Lgrid
  have hax : (axes : ℝ) ≤ Real.exp B := ha.trans (by linarith [Real.add_one_le_exp B])
  have hgx : (gridaxes : ℝ) ≤ Real.exp B := hg.trans (by linarith [Real.add_one_le_exp B])
  have hcut (z : ℝ) (hz : 1 ≤ z) : (axes : ℝ) * cutoff / (2 * z) ≤ Real.exp (2 * B) := by
    calc
      _ ≤ (axes : ℝ) * cutoff := div_le_self (mul_nonneg (Nat.cast_nonneg _) hc0) (by linarith)
      _ ≤ Real.exp B * Real.exp B := mul_le_mul hax hc hc0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← two_mul]
  have hfirst : (axes * cutoff / (2 * r)) * coord ≤ Real.exp (3 * B) := by
    calc
      _ ≤ Real.exp (2 * B) * Real.exp B := mul_le_mul (hcut r hr) hcoord hcoord0 (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsum : Real.exp (axes + 6 * Q + 12) + axes * cutoff / (2 * radius) ≤
      Real.exp (3 * B + 6 * Q + 13) := by
    have hs := add_le_exp_add_one (show 0 ≤ B + 6 * Q + 12 by positivity)
      (show 0 ≤ 2 * B by positivity)
      (Real.exp_le_exp.mpr (add_le_add (add_le_add ha le_rfl) le_rfl)) (hcut radius hradius)
    exact hs.trans_eq (by congr 1; ring)
  have hsecond : (Real.exp (axes + 6 * Q + 12) + axes * cutoff / (2 * radius)) * coord * Mp ≤
      Real.exp (4 * B + 6 * Q + Pper + 13) := by
    calc
      _ ≤ Real.exp (3 * B + 6 * Q + 13) * Real.exp B * Real.exp Pper :=
        mul_le_mul (mul_le_mul hsum hcoord hcoord0 (Real.exp_nonneg _)) hMp hMp0 (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hthird : 4 * Mp ≤ Real.exp (4 * B + 6 * Q + Pper + 13) := by
    calc
      _ ≤ Real.exp 4 * Real.exp Pper := mul_le_mul hfour hMp hMp0 (Real.exp_nonneg _)
      _ = Real.exp (4 + Pper) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hlong : Llong ≤ Real.exp (7 * B + 6 * Q + Pper + 14) := by
    have h := add_le_exp_add_one (show 0 ≤ 3 * B by positivity)
      (show 0 ≤ 4 * B + 6 * Q + Pper + 13 by positivity) hfirst (max_le hsecond hthird)
    exact h.trans_eq (by congr 1; ring)
  have hpower : (Real.exp Op) ^ gridaxes ≤ Real.exp (B * Op) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hg hOp)
  have hgridFirst : gridaxes * Real.exp Op * Qgrid * coord * (Real.exp Op) ^ gridaxes ≤
      Real.exp (3 * B + (B + 1) * Op) := by
    calc
      _ ≤ Real.exp B * Real.exp Op * Real.exp B * Real.exp B * Real.exp (B * Op) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hgrid : Lgrid ≤ Real.exp (3 * B + (B + 1) * Op + 4) := by
    apply max_le
    · exact hgridFirst.trans (Real.exp_le_exp.mpr (by linarith))
    · calc
        _ ≤ Real.exp 4 * Real.exp (B * Op) := mul_le_mul hfour hpower (by positivity) (Real.exp_nonneg _)
        _ = Real.exp (4 + B * Op) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hboth := add_le_exp_add_one (show 0 ≤ 7 * B + 6 * Q + Pper + 14 by positivity)
    (show 0 ≤ 3 * B + (B + 1) * Op + 4 by positivity) hlong hgrid
  have hcover : period * (Real.exp Op) ^ gridaxes ≤ Real.exp (Pper + B * Op) :=
    (mul_le_mul hper hpower (by positivity) (Real.exp_nonneg _)).trans_eq (Real.exp_add _ _).symm
  calc
    _ ≤ Real.exp ((7 * B + 6 * Q + Pper + 14) + (3 * B + (B + 1) * Op + 4) + 1) *
        Real.exp (Pper + B * Op) := mul_le_mul hboth hcover (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem allocatedAffineCover_exp_bound {B Op Pper period : ℝ}
    (gridaxes : ℕ) (hB : 0 ≤ B) (hOp : 0 ≤ Op)
    (hg : (gridaxes : ℝ) ≤ B) (hperiod : period ≤ Real.exp Pper) :
    period * (Real.exp Op) ^ gridaxes ≤ Real.exp (Pper + B * Op) := by
  have hpower : (Real.exp Op) ^ gridaxes ≤ Real.exp (B * Op) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (mul_le_mul hg le_rfl hOp hB)
  exact (mul_le_mul hperiod hpower (by positivity) (Real.exp_nonneg _)).trans_eq
    (Real.exp_add _ _).symm

theorem allocatedAffineFactor_nnreal_exp_bound {B Q Op Pper : ℝ}
    (cutoff coord Qgrid Mp period r radius : ℝ≥0) (axes gridaxes : ℕ)
    (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hOp : 0 ≤ Op) (hPper : 0 ≤ Pper)
    (ha : (axes : ℝ) ≤ B) (hg : (gridaxes : ℝ) ≤ B)
    (hc : (cutoff : ℝ) ≤ Real.exp B) (hcoord : (coord : ℝ) ≤ Real.exp B)
    (hQgrid : (Qgrid : ℝ) ≤ Real.exp B) (hMp : (Mp : ℝ) ≤ Real.exp Pper)
    (hper : (period : ℝ) ≤ Real.exp Pper) (hr : 1 ≤ r) (hradius : 1 ≤ radius) :
    let Llong : ℝ≥0 := (axes * cutoff / (2 * r)) * coord +
      max ((⟨Real.exp (axes + 6 * Q + 12), Real.exp_nonneg _⟩ + axes * cutoff / (2 * radius)) * coord * Mp) (4 * Mp)
    let Lprimitive : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg _⟩
    let Lgrid : ℝ≥0 := max (gridaxes * Lprimitive * Qgrid * coord * Lprimitive ^ gridaxes)
      (4 * Lprimitive ^ gridaxes)
    (((Llong + Lgrid) * (period * Lprimitive ^ gridaxes) : ℝ≥0) : ℝ) ≤
      Real.exp (10 * B + 6 * Q + 2 * Pper + (2 * B + 1) * Op + 19) := by
  exact
    allocatedAffineFactor_exp_bound axes gridaxes hB hQ hOp hPper ha hg
      cutoff.coe_nonneg coord.coe_nonneg Qgrid.coe_nonneg Mp.coe_nonneg period.coe_nonneg
      hc hcoord hQgrid hMp hper (show (1 : ℝ) ≤ r from hr) (show (1 : ℝ) ≤ radius from hradius)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_allocatedAffineModelMass_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p v F Prho Pk target : ℝ},
      0 ≤ D → 0 ≤ p → 0 ≤ v → 0 ≤ F → 0 ≤ Prho → 0 ≤ Pk → 0 ≤ target →
      ∀ (outputs axes gridaxes ambient : ℕ),
      (outputs : ℝ) ≤ D → (axes : ℝ) ≤ D → (gridaxes : ℝ) ≤ D → (ambient : ℝ) ≤ D →
      (dim : ℝ) ≤ D → (probabilityProfileLipschitz : ℝ) ≤ D →
      let Eg := outputs * Prho + (target + F) + 1
      let Op := allocatedSlicedGridResourceLog m dim D p v Eg
      let Plong := ((m : ℝ) + 2) * dim + m + 4 + Prho + axes * max Op 0 + (target + F) + 2
      let Q := idealSiteLogBudget outputs dim Plong
      2 * (2 : ℝ) ^ dim + F + (2 : ℝ) ^ dim * (ambient * ((m + 1 : ℕ) * Pk)) +
        ((2 : ℝ) ^ dim * axes * (4 * Q + 8) + Q) + gridaxes * Op ≤
        (D + p + v + F + Prho + Pk + target + A) ^ A := by
  obtain ⟨b, hb, hgrid⟩ := exists_allocatedSlicedGridResource_budget m dim
  let X : Polynomial ℕ := Polynomial.X
  let O : Polynomial ℕ := (3 * X + (X ^ 2 + 2 * X + 1) + Polynomial.C b) ^ b
  let Pbox : Polynomial ℕ := Polynomial.C ((m + 2) * dim + m + 4)
  let Pl : Polynomial ℕ := Pbox + X + X * O + 2 * X + 2
  let Qp := allocatedFiniteIdealProfileLog X Pl
  let poly : Polynomial ℕ := 2 * (2 : Polynomial ℕ) ^ dim + X + (2 : Polynomial ℕ) ^ dim *
    (X * ((m + 1 : ℕ) * X)) + ((2 : Polynomial ℕ) ^ dim * X * (4 * Qp + 8) + Qp) + X * O
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D p v F Prho Pk target hD hp hv hF hPrho hPk htarget outputs axes gridaxes ambient
    hout haxes hgridaxes hamb hdim hprofile Eg Op Plong Q
  let R := D + p + v + F + Prho + Pk + target
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hFR : F ≤ R := by dsimp [R]; linarith
  have hPrhoR : Prho ≤ R := by dsimp [R]; linarith
  have hPkR : Pk ≤ R := by dsimp [R]; linarith
  have htR : target ≤ R := by dsimp [R]; linarith
  have hEg : 0 ≤ Eg := by dsimp [Eg]; positivity
  have hEgR : Eg ≤ R ^ 2 + 2 * R + 1 := by
    have hprod := mul_le_mul (hout.trans hDR) hPrhoR hPrho hR
    dsimp only [Eg]
    nlinarith only [hprod, htR, hFR]
  let Ob := (3 * R + (R ^ 2 + 2 * R + 1) + b) ^ b
  have hOb : 0 ≤ Ob := by dsimp [Ob]; positivity
  have hOp : 0 ≤ Op := allocatedSlicedGridResourceLog_nonneg m dim hD hp hv hEg
  have hOpR : Op ≤ Ob := (hgrid hD hp hv hEg).trans
    (pow_le_pow_left₀ (by positivity) (by linarith only [hDR, hpR, hvR, hEgR]) b)
  let Plb := (((m + 2) * dim + m + 4 : ℕ) : ℝ) + R + R * Ob + 2 * R + 2
  have hPlb : 0 ≤ Plb := by dsimp [Plb]; positivity
  have hPl : 0 ≤ Plong := by dsimp [Plong]; positivity
  have hPlR : Plong ≤ Plb := by
    have hm : (axes : ℝ) * max Op 0 ≤ R * Ob := by
      rw [max_eq_left hOp]
      exact mul_le_mul (haxes.trans hDR) hOpR hOp hR
    dsimp only [Plong, Plb]
    push_cast
    linarith only [hPrhoR, htR, hFR, hm]
  let Qb := allocatedFiniteIdealProfileLog R Plb
  have hQb : 0 ≤ Qb := (allocatedFiniteIdeal_budget_nonneg m hR hPlb (le_refl (0 : ℝ))).1
  have hQ : 0 ≤ Q := (idealSiteLogBudget_bounds outputs dim hPl).1
  have hQR : Q ≤ Qb := by
    apply (idealSiteLogBudget_le_finite_profile hPl hout hdim hprofile).trans
    change allocatedFiniteIdealProfileLog D Plong ≤ allocatedFiniteIdealProfileLog R Plb
    unfold allocatedFiniteIdealProfileLog
    gcongr
  have hmass : 2 * (2 : ℝ) ^ dim + F + (2 : ℝ) ^ dim * (ambient * ((m + 1 : ℕ) * Pk)) +
      ((2 : ℝ) ^ dim * axes * (4 * Q + 8) + Q) + gridaxes * Op ≤
      2 * (2 : ℝ) ^ dim + R + (2 : ℝ) ^ dim * (R * ((m + 1 : ℕ) * R)) +
      ((2 : ℝ) ^ dim * R * (4 * Qb + 8) + Qb) + R * Ob := by
    gcongr
    · exact hamb.trans hDR
    · exact haxes.trans hDR
    · exact hgridaxes.trans hDR
  apply hmass.trans
  simpa [poly, X, O, Pbox, Pl, Qp, Ob, Plb, Qb, allocatedFiniteIdealProfileLog,
    Polynomial.eval₂_pow] using hbound R hR

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

theorem exists_allocatedAffineAnalytic_budget (m dim : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p v F Prho Pk target B : ℝ},
      0 ≤ D → 0 ≤ p → 0 ≤ v → 0 ≤ F → 0 ≤ Prho → 0 ≤ Pk → 0 ≤ target → 0 ≤ B →
      ∀ (outputs axes : ℕ), (outputs : ℝ) ≤ D → (axes : ℝ) ≤ D →
      (dim : ℝ) ≤ D → (probabilityProfileLipschitz : ℝ) ≤ D →
      let Eg := outputs * Prho + (target + F) + 1
      let Op := allocatedSlicedGridResourceLog m dim D p v Eg
      let Plong := ((m : ℝ) + 2) * dim + m + 4 + Prho + axes * max Op 0 + (target + F) + 2
      let Q := idealSiteLogBudget outputs dim Plong
      10 * B + 6 * Q + 2 * ((m + 1 : ℕ) * Pk) + (2 * B + 1) * Op + 19 ≤
        (D + p + v + F + Prho + Pk + target + B + A) ^ A := by
  obtain ⟨b, hb, hgrid⟩ := exists_allocatedSlicedGridResource_budget m dim
  let X : Polynomial ℕ := Polynomial.X
  let O : Polynomial ℕ := (3 * X + (X ^ 2 + 2 * X + 1) + Polynomial.C b) ^ b
  let Pbox : Polynomial ℕ := Polynomial.C ((m + 2) * dim + m + 4)
  let Pl : Polynomial ℕ := Pbox + X + X * O + 2 * X + 2
  let Qp := allocatedFiniteIdealProfileLog X Pl
  let poly : Polynomial ℕ := 10 * X + 6 * Qp + 2 * ((m + 1 : ℕ) * X) + (2 * X + 1) * O + 19
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro D p v F Prho Pk target B hD hp hv hF hPrho hPk htarget hB outputs axes
    hout haxes hdim hprofile Eg Op Plong Q
  let R := D + p + v + F + Prho + Pk + target + B
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hBR : B ≤ R := by dsimp [R]; linarith
  have hDR : D ≤ R := by dsimp [R]; linarith
  have hpR : p ≤ R := by dsimp [R]; linarith
  have hvR : v ≤ R := by dsimp [R]; linarith
  have hFR : F ≤ R := by dsimp [R]; linarith
  have hPrhoR : Prho ≤ R := by dsimp [R]; linarith
  have hPkR : Pk ≤ R := by dsimp [R]; linarith
  have htR : target ≤ R := by dsimp [R]; linarith
  have hEg : 0 ≤ Eg := by dsimp [Eg]; positivity
  have hEgR : Eg ≤ R ^ 2 + 2 * R + 1 := by
    have hprod := mul_le_mul (hout.trans hDR) hPrhoR hPrho hR
    dsimp only [Eg]
    nlinarith only [hprod, htR, hFR]
  let Ob := (3 * R + (R ^ 2 + 2 * R + 1) + b) ^ b
  have hOb : 0 ≤ Ob := by dsimp [Ob]; positivity
  have hOp : 0 ≤ Op := allocatedSlicedGridResourceLog_nonneg m dim hD hp hv hEg
  have hOpR : Op ≤ Ob := (hgrid hD hp hv hEg).trans
    (pow_le_pow_left₀ (by positivity) (by linarith only [hDR, hpR, hvR, hEgR]) b)
  let Plb := (((m + 2) * dim + m + 4 : ℕ) : ℝ) + R + R * Ob + 2 * R + 2
  have hPlb : 0 ≤ Plb := by dsimp [Plb]; positivity
  have hPl : 0 ≤ Plong := by dsimp [Plong]; positivity
  have hPlR : Plong ≤ Plb := by
    have hm : (axes : ℝ) * max Op 0 ≤ R * Ob := by
      rw [max_eq_left hOp]
      exact mul_le_mul (haxes.trans hDR) hOpR hOp hR
    dsimp only [Plong, Plb]
    push_cast
    linarith only [hPrhoR, htR, hFR, hm]
  let Qb := allocatedFiniteIdealProfileLog R Plb
  have hQb : 0 ≤ Qb := (allocatedFiniteIdeal_budget_nonneg m hR hPlb (le_refl (0 : ℝ))).1
  have hQ : 0 ≤ Q := (idealSiteLogBudget_bounds outputs dim hPl).1
  have hQR : Q ≤ Qb := by
    apply (idealSiteLogBudget_le_finite_profile hPl hout hdim hprofile).trans
    change allocatedFiniteIdealProfileLog D Plong ≤ allocatedFiniteIdealProfileLog R Plb
    unfold allocatedFiniteIdealProfileLog
    gcongr
  have hcost : 10 * B + 6 * Q + 2 * ((m + 1 : ℕ) * Pk) + (2 * B + 1) * Op + 19 ≤
      10 * R + 6 * Qb + 2 * ((m + 1 : ℕ) * R) + (2 * R + 1) * Ob + 19 := by
    gcongr
  apply hcost.trans
  simpa [poly, X, O, Pbox, Pl, Qp, Ob, Plb, Qb, allocatedFiniteIdealProfileLog,
    Polynomial.eval₂_pow] using hbound R hR

theorem allocatedAffineAnalytic_bounds (m dim outputs axes gridaxes : ℕ)
    {D p v F Prho Pk target B : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) (hF : 0 ≤ F)
    (hPrho : 0 ≤ Prho) (hPk : 0 ≤ Pk) (htarget : 0 ≤ target) (hB : 0 ≤ B)
    (hout : (outputs : ℝ) ≤ D) (haxes : (axes : ℝ) ≤ D)
    (hdim : (dim : ℝ) ≤ D) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D)
    (hDB : D ≤ B) (hgrid : (gridaxes : ℝ) ≤ B)
    (cutoff coord Qgrid r radius : ℝ≥0) (hr : 1 ≤ r) (hradius : 1 ≤ radius)
    (hc : (cutoff : ℝ) ≤ Real.exp B) (hcoord : (coord : ℝ) ≤ Real.exp B)
    (hQgrid : (Qgrid : ℝ) ≤ Real.exp B)
    (M period : ℕ) (hM : (M : ℝ) ≤ Real.exp Pk) (hperiod : period ≤ M ^ (m + 1)) :
    let A := Classical.choose (exists_allocatedAffineAnalytic_budget m dim)
    let Eg := outputs * Prho + (target + F) + 1
    let Op := allocatedSlicedGridResourceLog m dim D p v Eg
    let Plong := ((m : ℝ) + 2) * Fintype.card (Fin dim) + m + 4 + Prho + axes * max Op 0 + (target + F) + 2
    let Q := idealSiteLogBudget outputs (Fintype.card (Fin dim)) Plong
    let Llong : ℝ≥0 := (axes * cutoff / (2 * r)) * coord +
      max ((⟨Real.exp (axes + 6 * Q + 12), Real.exp_nonneg _⟩ + axes * cutoff / (2 * radius)) * coord * (M ^ (m + 1))) (4 * (M ^ (m + 1)))
    let Lprimitive : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg _⟩
    let Lgrid : ℝ≥0 := max (gridaxes * Lprimitive * Qgrid * coord * Lprimitive ^ gridaxes)
      (4 * Lprimitive ^ gridaxes)
    (((Llong + Lgrid) * (period * Lprimitive ^ gridaxes) : ℝ≥0) : ℝ) ≤
      Real.exp ((D + p + v + F + Prho + Pk + target + B + A) ^ A) ∧
    (period : ℝ) * (Real.exp Op) ^ gridaxes ≤
      Real.exp ((D + p + v + F + Prho + Pk + target + B + A) ^ A) := by
  intro A Eg Op Plong Q Llong Lprimitive Lgrid
  have hEg : 0 ≤ Eg := by dsimp only [Eg]; positivity
  have hOp := allocatedSlicedGridResourceLog_nonneg m dim hD hp hv hEg
  have hPlong : 0 ≤ Plong := by dsimp only [Plong]; positivity
  have hQ := (idealSiteLogBudget_bounds outputs (Fintype.card (Fin dim)) hPlong).1
  have hMp : ((M ^ (m + 1) : ℝ≥0) : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * Pk) := by
    change (M : ℝ) ^ (m + 1) ≤ _
    calc
      _ ≤ (Real.exp Pk) ^ (m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM _
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hper : (period : ℝ) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * Pk) :=
    (by exact_mod_cast hperiod : (period : ℝ) ≤ (M : ℝ) ^ (m + 1)).trans hMp
  have hlog : 10 * B + 6 * Q + 2 * (((m + 1 : ℕ) : ℝ) * Pk) + (2 * B + 1) * Op + 19 ≤
      (D + p + v + F + Prho + Pk + target + B + A) ^ A := by
    simpa only [Q, Plong, Fintype.card_fin] using
      (Classical.choose_spec (exists_allocatedAffineAnalytic_budget m dim)).2
        hD hp hv hF hPrho hPk htarget hB outputs axes hout haxes hdim hprofile
  exact ⟨(allocatedAffineFactor_nnreal_exp_bound cutoff coord Qgrid (M ^ (m + 1)) period r radius
    axes gridaxes hB hQ hOp (by positivity) (haxes.trans hDB) hgrid hc hcoord hQgrid hMp hper
    hr hradius).trans (Real.exp_le_exp.mpr hlog),
    (allocatedAffineCover_exp_bound gridaxes hB hOp hgrid hper).trans
      (Real.exp_le_exp.mpr (le_trans (by
        have hper0 : 0 ≤ (((m + 1 : ℕ) : ℝ) * Pk) := mul_nonneg (Nat.cast_nonneg _) hPk
        nlinarith only [hB, hQ, hOp, hper0, mul_nonneg hB hOp]) hlog))⟩

end Erdos3.VectorPolynomial

end

end OAI
