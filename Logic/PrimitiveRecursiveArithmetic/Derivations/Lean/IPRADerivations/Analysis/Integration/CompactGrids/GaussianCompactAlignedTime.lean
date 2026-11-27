import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactRiemannSplit

/-!
# Actual compact samples at equal represented times

This interface asks only for comparison at zero time distance. Both
precisions remain independent numerical inputs, and the conclusion is
exactly their two ordinary observation errors. No near-time modulus,
regular-name predicate or desired quadrature relation is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCompactAlignedTime

open_ipra
open GaussianCompactRiemannName (inside value sampledModulus sampled_modulus_at shift_sampled_modulus)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def body (F : PR 3) (a C E x p q t u : PTm n) : Fm PTm n :=
  inside a C E t ⟶ inside a C E u ⟶ distanceBounded (value t) (value u) zero one ⟶
    distanceBounded (ap3 F p t x) (ap3 F q u x) (unit p+unit q) (unit p*unit q)
ipra_subst body

def alignedSamples (F : PR 3) (a C E x : PTm n) : Fm PTm n := .all (.all (.all (.all
  (body F (Syn.shift (Syn.shift (Syn.shift (Syn.shift a)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift C))))
    (Syn.shift (Syn.shift (Syn.shift (Syn.shift E)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift x))))
    (var 3) (var 2) (var 1) (var 0)))))
ipra_subst alignedSamples [Syn.subst_shift, Syn.shift_subst, Syn.up]

theorem aligned_at (F : PR 3) (p q a C E x t u : PTm n)
    (h : Γ ⊢[PRAAx] alignedSamples F a C E x) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (value t) (value u) zero one) : Γ ⊢[PRAAx]
    distanceBounded (ap3 F p t x) (ap3 F q u x) (unit p+unit q) (unit p*unit q) := by
  have rule : Γ ⊢[PRAAx] body F a C E x p q t u := by
    simpa only [alignedSamples,Fm.subst_all,subst_body,Foundations.BoundedFormulas.subst_up_shift',
      Syn.subst_var,GaussianCompactRiemannName.up_three,GaussianCompactRiemannName.up_two,Syn.up_one,Syn.up_zero,Syn.up_succ,
      Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,Syn.shift_var] using (((h.allE p).allE q).allE t).allE u
  exact .impE (.impE (.impE rule ht) hu) hd

theorem equal_value_at (F : PR 3) (s a C E x t u : PTm n)
    (h : Γ ⊢[PRAAx] alignedSamples F a C E x) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (he : Γ ⊢[PRAAx] value t ≐ value u) : Γ ⊢[PRAAx]
    distanceBounded (ap3 F s t x) (ap3 F s u x) two (unit s) := by
  have metric := distance_congr he.eqSymm (.eqRefl _) (.eqRefl zero) (.eqRefl one)
    (GaussianRationalPowerDifference.distance_refl_zero (value u) one (le_refl one))
  have raw := aligned_at F s s a C E x t u h ht hu metric
  exact distance_radius_mono _ _ _ _ two (unit s)
    (GaussianRationalHorner.positive_product _ _ (unit_positive s) (unit_positive s)) (unit_positive s)
    (le_of_eq_add (d := zero) (by ipra_ring)) raw

theorem modulus_observations (F : PR 3) (p q a C E L x t u : PTm n)
    (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (value t) (value u) zero one) : Γ ⊢[PRAAx]
    distanceBounded (ap3 F p t x) (ap3 F q u x) (unit p+unit q) (unit p*unit q) := by
  have actual := sampled_modulus_at F a C E L x p q t u zero one h (le_refl one) ht hu hd
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _)
    (by unfold GaussianNamedInverseRate.rateNumerator; ipra_ring)
    (by unfold GaussianNamedInverseRate.rateDenominator; ipra_ring) actual

theorem of_sampled_modulus (F : PR 3) (a C E L x : PTm n) (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) : Γ ⊢[PRAAx]
    alignedSamples F a C E x := by
  have hs := shift_sampled_modulus <| shift_sampled_modulus <|
    shift_sampled_modulus <| shift_sampled_modulus h
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI ?_))))))
  simpa only [body,Syn.shift] using modulus_observations F (var 3) (var 2) _ _ _ _ _ (var 1) (var 0) hs.wk.wk.wk
    Prf.hyp1.wk Prf.hyp1 Prf.hyp0

theorem left_aligned (F : PR 3) (a C1 C2 E x : PTm n) (h : Γ ⊢[PRAAx] alignedSamples F a (C1+C2) E x) : Γ ⊢[PRAAx]
    alignedSamples F a C1 E x := by
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      alignedSamples F (Syn.shift (Syn.shift (Syn.shift (Syn.shift a))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift C1)))+Syn.shift (Syn.shift (Syn.shift (Syn.shift C2))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift E)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift x)))) :=
    by simpa [Fm.shift,Syn.shift] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI ?_))))))
  simpa only [body,PTm.subst_add,Syn.shift] using aligned_at F (var 3) (var 2) _ _ _ _ (var 1) (var 0) hs.wk.wk.wk
    (GaussianCompactRiemannSplit.inside_left _ _ _ _ _ Prf.hyp1.wk)
    (GaussianCompactRiemannSplit.inside_left _ _ _ _ _ Prf.hyp1) Prf.hyp0

theorem right_aligned (F : PR 3) (a C1 C2 E x : PTm n) (h : Γ ⊢[PRAAx] alignedSamples F a (C1+C2) E x) : Γ ⊢[PRAAx]
    alignedSamples F (a+C1) C2 E x := by
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      alignedSamples F (Syn.shift (Syn.shift (Syn.shift (Syn.shift a))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift C1)))+Syn.shift (Syn.shift (Syn.shift (Syn.shift C2))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift E)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift x)))) :=
    by simpa [Fm.shift,Syn.shift] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI ?_))))))
  simpa only [body,PTm.subst_add,Syn.shift] using aligned_at F (var 3) (var 2) _ _ _ _ (var 1) (var 0) hs.wk.wk.wk
    (GaussianCompactRiemannSplit.inside_right _ _ _ _ _ Prf.hyp1.wk)
    (GaussianCompactRiemannSplit.inside_right _ _ _ _ _ Prf.hyp1) Prf.hyp0

theorem actual_equal_time_independent_queries_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((alignedSamples F (var 2) (var 3) (var 4) (var 5) ⋏ inside (var 2) (var 3) (var 4) (var 6) ⋏
      inside (var 2) (var 3) (var 4) (var 7) ⋏ distanceBounded (value (var 6)) (value (var 7)) zero one) ⟶
      distanceBounded (ap3 F (var 0) (var 6) (var 5)) (ap3 F (var 1) (var 7) (var 5))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (aligned_at F _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianCompactAlignedTime
