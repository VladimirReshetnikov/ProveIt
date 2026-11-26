import IPRADerivations.Analysis.Names.GaussianCompactNamedAdditivity
import IPRADerivations.Analysis.Polynomials.Horner.GaussianReciprocalHorner

/-!
# Compact tail bounds from a common reference

If the full compact integral and either subinterval integral are close
to the same reference at the same observation clock, additivity bounds
the other subinterval. The error accounts for the actual normalized
sum name and the literal rational sum of the two observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactTailFromComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactNamedAdditivity (input name_additivity left_input right_input)
open GaussianCompactRiemannName (nameF data name_regular name_canonical)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (canonical positive_product qadd)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qadd_sub_cancel)
open GaussianNameEquivalence (cross_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def observation (F : PR 3) (p a C E L T x : PTm n) : PTm n := ap2 (nameF F) p (data a C E L T x)

@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (F : PR 3) (p a C E L T x : PTm n) :
    Syn.subst σ (observation F p a C E L T x) = observation F (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ C)
      (Syn.subst σ E) (Syn.subst σ L) (Syn.subst σ T) (Syn.subst σ x) := by simp [observation]

theorem observation_additivity (F : PR 3) (p a C1 C2 E L T x : PTm n)
    (h : Γ ⊢[PRAAx] input F a C1 C2 E L T x) : Γ ⊢[PRAAx]
    distanceBounded (observation F p a (C1+C2) E L T x)
      (qadd (observation F p a C1 E L T x) (observation F p (a+C1) C2 E L T x)) (num 5) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have cross := cross_at _ _ _ _ p p (name_additivity F a C1 C2 E L T x h)
  have near := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by ipra_ring)) cross
  have rounded := GaussianNameRingLaws.add_sample_error (nameF F) (nameF F)
    (data a C1 E L T x) (data (a+C1) C2 E L T x) p
    (name_regular F a C1 E L T x (left_input F a C1 C2 E L T x h))
    (name_regular F (a+C1) C2 E L T x (right_input F a C1 C2 E L T x h))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp near rounded)

private theorem other_bound (full known other v p s : PTm n)
    (hc : Γ ⊢[PRAAx] canonical other) (hadd : Γ ⊢[PRAAx] distanceBounded full (qadd known other) (num 5) (unit p))
    (hfull : Γ ⊢[PRAAx] distanceBounded full v (unit p+two*unit s) (unit s*unit p))
    (hknown : Γ ⊢[PRAAx] distanceBounded known v (unit p+two*unit s) (unit s*unit p)) : Γ ⊢[PRAAx]
    bounded other (two*unit p+num 9*unit s) (unit s*unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ (unit_positive s) hp
  have sumNear := distance_radius_mono _ _ _ _ (num 5*unit s) (unit s*unit p) hp hd
    (le_of_eq_add (d := zero) (by ipra_ring)) (distance_symmetric _ _ _ _ hp hadd)
  have piecesNear := distance_triangle_same _ v _ _ _ _ hd hfull (distance_symmetric _ _ _ _ hd hknown)
  have joined := distance_triangle_same _ full _ _ _ _ hd sumNear piecesNear
  exact bound_congr (qadd_sub_cancel known other hc) (by ipra_ring) (.eqRefl _) joined

theorem suffix_bound (F : PR 3) (p s a C1 C2 E L T x v : PTm n)
    (hadd : Γ ⊢[PRAAx] input F a C1 C2 E L T x)
    (hfull : Γ ⊢[PRAAx] distanceBounded (observation F p a (C1+C2) E L T x) v
      (unit p+two*unit s) (unit s*unit p))
    (hprefix : Γ ⊢[PRAAx] distanceBounded (observation F p a C1 E L T x) v
      (unit p+two*unit s) (unit s*unit p)) : Γ ⊢[PRAAx]
    bounded (observation F p (a+C1) C2 E L T x) (two*unit p+num 9*unit s) (unit s*unit p) :=
  other_bound _ _ _ v p s (name_canonical F p (a+C1) C2 E L T x)
    (observation_additivity F p a C1 C2 E L T x hadd) hfull hprefix

theorem prefix_bound (F : PR 3) (p s a C1 C2 E L T x v : PTm n)
    (hadd : Γ ⊢[PRAAx] input F a C1 C2 E L T x)
    (hfull : Γ ⊢[PRAAx] distanceBounded (observation F p a (C1+C2) E L T x) v
      (unit p+two*unit s) (unit s*unit p))
    (hsuffix : Γ ⊢[PRAAx] distanceBounded (observation F p (a+C1) C2 E L T x) v
      (unit p+two*unit s) (unit s*unit p)) : Γ ⊢[PRAAx]
    bounded (observation F p a C1 E L T x) (two*unit p+num 9*unit s) (unit s*unit p) :=
  other_bound _ _ _ v p s (name_canonical F p a C1 E L T x)
    (distance_congr (.eqRefl _) (GaussianReciprocalHorner.qadd_commutative _ _) (.eqRefl _) (.eqRefl _)
      (observation_additivity F p a C1 C2 E L T x hadd)) hfull hsuffix

theorem actual_compact_suffix_from_common_comparison_closed (F : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (input F (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        distanceBounded (observation F (var 0) (var 2) (var 3+var 4) (var 5) (var 6) (var 7) (var 8)) (var 9)
          (unit (var 0)+two*unit (var 1)) (unit (var 1)*unit (var 0)) ⟶
        distanceBounded (observation F (var 0) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8)) (var 9)
          (unit (var 0)+two*unit (var 1)) (unit (var 1)*unit (var 0)) ⟶
        bounded (observation F (var 0) (var 2+var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
          (two*unit (var 0)+num 9*unit (var 1)) (unit (var 1)*unit (var 0))) :=
  closeUniv 10 (.impI (.impI (.impI (suffix_bound F _ _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_compact_prefix_from_common_comparison_closed (F : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (input F (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        distanceBounded (observation F (var 0) (var 2) (var 3+var 4) (var 5) (var 6) (var 7) (var 8)) (var 9)
          (unit (var 0)+two*unit (var 1)) (unit (var 1)*unit (var 0)) ⟶
        distanceBounded (observation F (var 0) (var 2+var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) (var 9)
          (unit (var 0)+two*unit (var 1)) (unit (var 1)*unit (var 0)) ⟶
        bounded (observation F (var 0) (var 2) (var 3) (var 5) (var 6) (var 7) (var 8))
          (two*unit (var 0)+num 9*unit (var 1)) (unit (var 1)*unit (var 0))) :=
  closeUniv 10 (.impI (.impI (.impI (prefix_bound F _ _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianCompactTailFromComparison
