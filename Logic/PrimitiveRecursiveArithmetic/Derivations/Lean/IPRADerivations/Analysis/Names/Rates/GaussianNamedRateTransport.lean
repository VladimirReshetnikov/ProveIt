import IPRADerivations.Analysis.Names.Rates.GaussianNamedInverseRate

/-!
# Exact rate transport between actual Gaussian names

An independent two-observation estimate is preserved when either program
is replaced by a cross-equivalent program. The requested observations
retain exactly their original dyadic errors. A common auxiliary precision
contributes four dyadic errors; rational slack removal eliminates these.
No regularity or canonical-code premise is needed beyond the supplied
cross-equivalences.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRateTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem observation_slack (F G H K : PR 2) (x y u v D N p q t : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] independentRate F G x y D N)
    (hl : Γ ⊢[PRAAx] crossEquivalent H F u x)
    (hr : Γ ⊢[PRAAx] crossEquivalent K G v y) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 H p u) (ap2 K q v))
      (rateNumerator D N p q) (rateDenominator N p q) (two*two) t := by
  let Z := rateDenominator N p q*unit t
  have z : Γ ⊢[PRAAx] le one Z := positive_product _ _ (denominator_positive N p q hN) (unit_positive t)
  have left := distance_radius_mono _ _ _ _ ((unit p+unit t)*(N*unit q)) Z
    (positive_product _ _ (unit_positive p) (unit_positive t)) z
    (le_of_eq_add (d := zero) (by dsimp only [Z,rateDenominator]; ipra_ring))
    (GaussianNameEquivalence.cross_at H F u x p t hl)
  have middle := distance_radius_mono _ _ _ _ ((D*unit t+two*N)*(unit p*unit q)) Z
    (positive_product _ _ hN (unit_positive t)) z
    (le_of_eq_add (d := zero) (by dsimp only [Z,rateDenominator]; ipra_ring))
    (GaussianNamedInverseRate.diagonal_rate F G x y D N t hN h)
  have right := distance_radius_mono _ _ _ _ ((unit t+unit q)*(N*unit p)) Z
    (positive_product _ _ (unit_positive t) (unit_positive q)) z
    (le_of_eq_add (d := zero) (by dsimp only [Z,rateDenominator]; ipra_ring))
    (GaussianNameEquivalence.cross_at G K y v t q (GaussianNameEquivalence.cross_symm _ _ _ _ hr))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [rateNumerator,rateDenominator,unit]; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ z (distance_triangle_same _ _ _ _ _ _ z left middle) right)

theorem observation_error (F G H K : PR 2) (x y u v D N p q : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] independentRate F G x y D N)
    (hl : Γ ⊢[PRAAx] crossEquivalent H F u x)
    (hr : Γ ⊢[PRAAx] crossEquivalent K G v y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 H p u) (ap2 K q v) (rateNumerator D N p q) (rateDenominator N p q) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (two*two) (denominator_positive N p q hN)
  refine .allI ?_
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] independentRate F G (Syn.shift x) (Syn.shift y) (Syn.shift D) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have ls : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent H F (Syn.shift u) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hl.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent K G (Syn.shift v) (Syn.shift y) := by simpa [Fm.shift,Syn.shift] using hr.shift
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,subst_ap2,
    GaussianNamedInverseRate.subst_rateNumerator,GaussianNamedInverseRate.subst_rateDenominator,
    PTm.subst_mul,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    observation_slack F G H K (Syn.shift x) (Syn.shift y) (Syn.shift u) (Syn.shift v) (Syn.shift D) (Syn.shift N)
      (Syn.shift p) (Syn.shift q) (var 0) ns hs ls rs

theorem transport (F G H K : PR 2) (x y u v D N : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] independentRate F G x y D N)
    (hl : Γ ⊢[PRAAx] crossEquivalent H F u x)
    (hr : Γ ⊢[PRAAx] crossEquivalent K G v y) : Γ ⊢[PRAAx] independentRate H K u v D N := by
  refine .allI (.allI ?_)
  have ns : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using hN.shift.shift
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] independentRate F G (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y))
      (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift N)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  have ls : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] crossEquivalent H F (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using hl.shift.shift
  have rs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] crossEquivalent K G (Syn.shift (Syn.shift v)) (Syn.shift (Syn.shift y)) := by
    simpa [Fm.shift,Syn.shift] using hr.shift.shift
  simpa only [independentRate,Syn.shift] using observation_error F G H K
    (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift v))
    (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift N)) (var 1) (var 0) ns hs ls rs

theorem exact_independent_rate_transport_closed (F G H K : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 5) ⋏ (independentRate F G (var 0) (var 1) (var 4) (var 5) ⋏
      (crossEquivalent H F (var 2) (var 0) ⋏ crossEquivalent K G (var 3) (var 1)))) ⟶
      independentRate H K (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (transport F G H K _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedRateTransport
