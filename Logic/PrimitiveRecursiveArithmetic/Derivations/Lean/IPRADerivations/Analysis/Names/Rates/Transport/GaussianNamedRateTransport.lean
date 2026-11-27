import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

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

open_ipra
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive shift_independent_rate)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianCoefficientNameBounds (unit)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr distance_through_auxiliary)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem observation_slack (F G H K : PR 2) (x y u v D N p q t : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] independentRate F G x y D N)
    (hl : Γ ⊢[PRAAx] crossEquivalent H F u x)
    (hr : Γ ⊢[PRAAx] crossEquivalent K G v y) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (ap2 H p u) (ap2 K q v))
      (rateNumerator D N p q) (rateDenominator N p q) (two*two) t := by
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [rateNumerator,rateDenominator,unit]; ipra_ring) (.eqRefl _)
    (distance_through_auxiliary p q t D N two hN
      (GaussianNameEquivalence.cross_at H F u x p t hl)
      (GaussianNamedInverseRate.diagonal_rate F G x y D N t hN h)
      (GaussianNameEquivalence.cross_at G K y v t q (GaussianNameEquivalence.cross_symm _ _ _ _ hr)))

theorem observation_error (F G H K : PR 2) (x y u v D N p q : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] independentRate F G x y D N)
    (hl : Γ ⊢[PRAAx] crossEquivalent H F u x)
    (hr : Γ ⊢[PRAAx] crossEquivalent K G v y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 H p u) (ap2 K q v) (rateNumerator D N p q) (rateDenominator N p q) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (two*two) (denominator_positive N p q hN)
  refine .allI ?_
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have hs := shift_independent_rate h
  have ls := GaussianNameEquivalence.shift_crossEquivalent hl
  have rs := GaussianNameEquivalence.shift_crossEquivalent hr
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
  have hs := shift_independent_rate (shift_independent_rate h)
  have ls := GaussianNameEquivalence.shift_crossEquivalent (GaussianNameEquivalence.shift_crossEquivalent hl)
  have rs := GaussianNameEquivalence.shift_crossEquivalent (GaussianNameEquivalence.shift_crossEquivalent hr)
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
