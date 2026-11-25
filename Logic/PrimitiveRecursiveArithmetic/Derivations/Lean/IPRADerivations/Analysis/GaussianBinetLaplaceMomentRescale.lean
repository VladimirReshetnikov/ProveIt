import IPRADerivations.Analysis.GaussianBinetLaplaceMomentImproperTaylor
import IPRADerivations.Analysis.GaussianEulerWeightedHalfDecay
import IPRADerivations.Analysis.GaussianLogGammaEulerResidualRadius

/-!
# Rational chart invariance of actual improper Binet moments

The existing right Taylor comparison at zero displacement binds two
proportional charts of the original evaluator. Finite slack removal
gives exact name equivalence. A shared denominator extends the result
to any two presentations with the same cross product.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentRescale

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceMomentImproper (nameF data subst_data regular sample_canonical)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint radius_congr)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qmul qzero positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr qmul_zero_left)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source

theorem data_congr (j X D R Y E : PTm n)
    (hX : Γ ⊢[PRAAx] X ≐ Y) (hD : Γ ⊢[PRAAx] D ≐ E) :
    Γ ⊢[PRAAx] data j X D R ≐ data j Y E R := by
  let t : PTm 4 := data (var 0) (var 1) (var 2) (var 3)
  simpa only [t,subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) t (σ := ![j,X,D,R]) (σ' := ![j,Y,E,R])
      (fun i => by fin_cases i; exact .eqRefl _; exact hX; exact hD; exact .eqRefl _)

theorem source_congr (X D R Y E : PTm n) (hX : Γ ⊢[PRAAx] X ≐ Y) (hD : Γ ⊢[PRAAx] D ≐ E)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R) : Γ ⊢[PRAAx] realSource Y zero E zero R := by
  let t : Fm PTm 3 := realSource (var 0) zero (var 1) zero (var 2)
  have hs : Γ ⊢[PRAAx] t.subst (![X,D,R] : Fin 3 → PTm n) := by
    simpa [t] using h
  simpa [t] using Prf.eqSubst t (![X,D,R] : Fin 3 → PTm n) (![Y,E,R] : Fin 3 → PTm n)
    (fun i => by fin_cases i; exact hX; exact hD; exact .eqRefl _) hs

private theorem zero_radius (K : PTm n) (hK : Γ ⊢[PRAAx] le one K) :
    Γ ⊢[PRAAx] radiusPoint zero K ≐ qzero :=
  (radius_congr (zero_mul K).eqSymm (one_mul K).eqSymm).eqTrans
    (GaussianEulerWeightedHalfDecay.radius_rescale zero one K (le_refl one) hK)

theorem diagonal_rescale (p j X D R S K : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (h' : Γ ⊢[PRAAx] realSource (X*K) zero (D*K) zero S)
    (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data j X D R)) (ap2 nameF p (data j (X*K) (D*K) S)) (num 10) (unit p) := by
  let a := X*K+zero*D
  let b := D*K
  let x := ap2 nameF p (data j X D R)
  let z := ap2 nameF p (data (succ j) X D R)
  have eA : Γ ⊢[PRAAx] a ≐ X*K := by dsimp only [a]; ipra_ring
  have he := data_congr j a b S (X*K) b eA (.eqRefl _)
  have hp := unit_positive (Γ := Γ) p
  have hraw := GaussianBinetLaplaceMomentImproperTaylor.observation_taylor p j X D R S zero K h
    (source_congr (X*K) b S a b eA.eqSymm (.eqRefl _) h') hK (zero_le K)
  have e0 : Γ ⊢[PRAAx] qmul (radiusPoint zero K) z ≐ qzero :=
    (qmul_congr (zero_radius K hK) (.eqRefl _)).eqTrans (qmul_zero_left z)
  have eLin : Γ ⊢[PRAAx] GaussianBinetLaplaceMomentImproperTaylor.linearSample p j X D R zero K ≐ x :=
    (qsub_congr (.eqRefl _) e0).eqTrans
      (GaussianRationalReconstruction.qsub_zero_right x (sample_canonical p j X D R))
  have hd := distance_radius_mono _ _ _ _ (num 10) (unit p)
    (positive_product _ _ (positive_product _ _ hK hK) hp) hp
    (le_of_eq_add (d := zero) (by unfold GaussianBinetLaplaceMomentImproperTaylor.leading; ipra_ring)) hraw
  exact GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hp
    (distance_congr (congrAp2 nameF (.eqRefl _) he) eLin (.eqRefl _) (.eqRefl _) hd)

private theorem zero_rate_cross (x y : PTm n)
    (hr : Γ ⊢[PRAAx] independentRate nameF nameF x y zero one) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF x y := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : Δ ⊢[PRAAx] independentRate nameF nameF (sh x) (sh y) zero one := by
    simpa only [Δ, sh, Fm.shift, GaussianNamedInverseRate.subst_independentRate, Syn.shift, one,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using hr.shift.shift
  refine .allI (.allI ?_)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring)
    (by unfold rateDenominator; ipra_ring) (rate_at nameF nameF (sh x) (sh y) zero one (var 1) (var 0) hs)

theorem rescale (j X D R S K : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (h' : Γ ⊢[PRAAx] realSource (X*K) zero (D*K) zero S)
    (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data j X D R) (data j (X*K) (D*K) S) := by
  apply zero_rate_cross
  apply GaussianNamedLipschitzRate.independent_rate nameF nameF _ _ zero one (num 10) (le_refl one)
    (regular _ _ _ _ h) (regular _ _ _ _ h')
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] realSource (s X) zero (s D) zero (s R) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source,
      ConciseIPRA.PTm.subst_zero] using h.shift
  have rs : Δ ⊢[PRAAx] realSource (s X*s K) zero (s D*s K) zero (s S) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source,PTm.subst_mul,
      ConciseIPRA.PTm.subst_zero] using h'.shift
  have ks : Δ ⊢[PRAAx] le one (s K) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hK.shift
  have left : Syn.shift (data j X D R) = data (s j) (s X) (s D) (s R) := subst_data _ _ _ _ _
  have right : Syn.shift (data j (X*K) (D*K) S) = data (s j) (s X*s K) (s D*s K) (s S) := by
    simp only [Syn.shift,s,subst_data,PTm.subst_mul]
  change Δ ⊢[PRAAx] distanceBounded (ap2 nameF (var 0) (Syn.shift (data j X D R)))
    (ap2 nameF (var 0) (Syn.shift (data j (X*K) (D*K) S)))
    (GaussianNamedLipschitzRate.diagonalNumerator (Syn.shift zero) (Syn.shift one) (Syn.shift (num 10)) (var 0))
    (GaussianNamedLipschitzRate.diagonalDenominator (Syn.shift one) (var 0))
  rw [left,right]
  exact distance_congr (.eqRefl _) (.eqRefl _) (by simp only [GaussianNamedLipschitzRate.diagonalNumerator,
    Syn.shift,PTm.subst_num,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]; ipra_ring)
    (by simp only [GaussianNamedLipschitzRate.diagonalDenominator,Syn.shift,one,ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero]; ipra_ring)
    (diagonal_rescale (var 0) (s j) (s X) (s D) (s R) (s S) (s K) hs rs ks)

theorem rational_proper (j X D R Y E S : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (h' : Γ ⊢[PRAAx] realSource Y zero E zero S)
    (hEq : Γ ⊢[PRAAx] X*E ≐ Y*D) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data j X D R) (data j Y E S) := by
  let T := GaussianLogGammaEulerResidualRadius.radius (X*E) zero
  have hD := h.andE₁.andE₂
  have hE := h'.andE₁.andE₂
  have hmid : Γ ⊢[PRAAx] realSource (X*E) zero (D*E) zero T :=
    GaussianLogGammaEulerResidualRadius.source_of_right_half_plane _ _ _ _
      (.andI (.andI (positive_product _ _ h.andE₁.andE₁.andE₁ hE) (.orI₁ (.eqRefl zero)))
        (positive_product _ _ hD hE))
  have same := mul_comm (Γ := Γ) D E
  have left := rescale j X D R T E h hmid hE
  have right := rescale j Y E S T D h' (source_congr _ _ _ _ _ hEq same hmid) hD
  have endRight := GaussianGammaCompactCutoffAlignment.cross_data_congr nameF nameF _ _ _ _ (.eqRefl _)
    (data_congr j (Y*D) (E*D) T (X*E) (D*E) hEq.eqSymm same.eqSymm) right
  exact cross_trans _ _ _ _ _ _ left (cross_symm _ _ _ _ endRight)

theorem actual_improper_Binet_moment_rational_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let j := var 0
     let X := var 1
     let D := var 2
     let R := var 3
     let Y := var 4
     let E := var 5
     let S := var 6
     (realSource X zero D zero R ⋏ realSource Y zero E zero S) ⟶ X*E ≐ Y*D ⟶
      crossEquivalent nameF nameF (data j X D R) (data j Y E S)) :=
  closeUniv 7 (.impI (.impI (rational_proper _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentRescale
