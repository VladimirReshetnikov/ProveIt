import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaNegativeCriticalLocation
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaReal
import IPRADerivations.Analysis.Names.RationalGaussianNameEmbedding

/-!
# Gaussian residual at the selected negative rational location

The correction is exactly real. The original shifted digamma therefore
has a real-axis representative obtained from the positive digamma
representative with the same correction. This lifts the scalar endpoint
error to the original Gaussian name at an independent observation clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLocationResidual

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaDigammaDyadicMesh (clock grid_scale)
open GaussianGammaNegativeCriticalCorrection
  (guard correction positiveSum row prefix_succ body bottomDen row_den_positive)
open GaussianGammaNegativeCriticalEndpoints (nameF nameData shifted_source mesh)
open GaussianGammaNegativeCriticalGrid (denominator residual_bound)
open GaussianGammaNegativeCriticalLocation (lower lower_guard denominator_positive)
open GaussianGammaNegativeCriticalSlope (coefficient)
open GaussianNameArithmetic (addF addData add_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_at cross_to_diagonal cross_refl)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded qsub_canonical)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianStirlingNames (fraction_axis add_real constant_real)
open RationalGaussianEmbedding (axis axis_congr axis_zero axis_add axis_negative scalarZero canonical_axis_roundtrip embed_zero)
open RationalGaussianNameEmbedding (distance_from_radius)
open RationalValueBounds (radius_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data
local notation "RF" => GaussianGammaDigammaReal.nameF
local notation "rd" => GaussianGammaDigammaReal.data

def realF : PR 2 := addF RF constantF
def realData (a b N : PTm n) : PTm n := addData (rd (b+a) b) (correction a b N)
def residualCost (N : PTm n) : PTm n := coefficient N (mesh N)+two*mesh N

ipra_subst residualCost

def prefixAxis (a b N : PTm n) : Fm PTm n := axis (positiveSum a b N)
ipra_subst prefixAxis

theorem prefix_axis (a b N : PTm n) (h : Γ ⊢[PRAAx] lt a b) :
    Γ ⊢[PRAAx] prefixAxis a b N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift a) (Syn.shift b) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have all : Γ ⊢[PRAAx] .all (prefixAxis (Syn.shift a) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ (by simp [prefixAxis,axis,RationalArgmin.rationalEq,Fm.QF]) ?_ ?_
    · simpa only [subst_prefixAxis,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
        (show Γ ⊢[PRAAx] prefixAxis a b zero from
          axis_congr (GaussianRationalFiniteSum.sum_zero body (pairT a b)).eqSymm axis_zero)
    · simp only [subst_prefixAxis,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let A := Syn.shift a
      let B := Syn.shift b
      exact axis_congr (prefix_succ A B (var 0)).eqSymm (axis_add _ _ Prf.hyp0
        (fraction_axis B (bottomDen A B (var 0)) (row_den_positive A B (var 0) hs.wk)))
  simpa only [subst_prefixAxis,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

theorem correction_axis (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] axis (correction a b N) :=
  axis_add _ _ (prefix_axis a b (succ N) h.andE₂) (axis_negative _ (fraction_axis b a h.andE₁))

theorem real_samples (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] realSamples realF (realData a b N) :=
  add_real RF constantF (rd (b+a) b) (correction a b N) (GaussianGammaDigammaReal.name_real (b+a) b)
    (constant_real _ (qsub_canonical _ _) (correction_axis a b N h))

theorem original_cross (a b N : PTm n) (h : Γ ⊢[PRAAx] guard a b) :
    Γ ⊢[PRAAx] crossEquivalent nameF realF (nameData a b N) (realData a b N) := by
  let d := correction a b N
  have hs := shifted_source a b h
  exact add_equivalent DF RF constantF constantF (dd (b+a) b) (rd (b+a) b) d d
    (GaussianGammaDigammaNative.name_regular _ _ hs) (GaussianGammaDigammaReal.name_regular _ _ hs)
    (constant_regular d) (constant_regular d)
    (cross_to_diagonal _ _ _ _ (GaussianGammaDigammaReal.original_cross (b+a) b hs))
    (cross_to_diagonal _ _ _ _ (cross_refl _ _ (constant_regular d)))

theorem original_residual_at (p q N : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF q (nameData (lower p N) (denominator p N) N)) qzero
      (residualCost N*unit q+denominator p N) (denominator p N*unit q) := by
  let B := denominator p N
  let a := lower p N
  let M := mesh N
  let E := coefficient N M+M
  let t := succ (clock p)
  let W := unit (clock p)
  let V := unit t
  let T := unit q
  let Y := ap2 realF t (realData a B N)
  let Z := ap2 nameF (clock p) (nameData a B N)
  have hb := denominator_positive (Γ := Γ) p N
  have hw := unit_positive (Γ := Γ) (clock p)
  have hv := unit_positive (Γ := Γ) t
  have hq := unit_positive (Γ := Γ) q
  have hs := lower_guard (Γ := Γ) p N
  have eq := original_cross a B N hs
  have hWV := positive_product W V hw hv
  have prior : Γ ⊢[PRAAx] distanceBounded Z Y (W+V) (W*V) :=
    cross_at nameF realF (nameData a B N) (realData a B N) (clock p) t eq
  have scalar := scalar_coordinate_distance Y Z _ _ hWV (distance_symmetric _ _ _ _ hWV prior)
  have little := radius_triangle (fstT Y) (fstT Z) scalarZero _ _ E B scalar (residual_bound p N)
  have real := real_sample_at realF (realData a B N) t (real_samples a B N hs)
  have hsmall := positive_product _ _ hWV hb
  have real_residual := distance_congr (canonical_axis_roundtrip Y real.andE₁ real.andE₂) embed_zero
    (.eqRefl _) (.eqRefl _) (distance_from_radius _ _ _ _ hsmall little)
  have hTV := positive_product T V hq hv
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hTV hsmall
    (cross_at nameF realF (nameData a B N) (realData a B N) q t eq) real_residual
  have ev : Γ ⊢[PRAAx] V ≐ W*two := pw_succ two (clock p)
  have u : 𝔞(V)=2*𝔞(W) := by
    have e := natEq ev
    ipra_simps
    linear_combination e
  have hBW := positive_product B W hb hw
  have main := distance_radius_mono _ _ _ _ (E*W*T+two*B*T+B*W) (B*W*T)
    (positive_product _ _ hTV hsmall) (positive_product _ _ hBW hq)
    (by ipra_le 0 using rw [u]; ring) joined
  have eW := natEq (show Γ ⊢[PRAAx] W ≐ num 64*unit p from grid_scale p)
  have spare : Γ ⊢[PRAAx] le (two*B) (M*W) := by
    dsimp only [M,B,denominator]
    ipra_le 62*𝔞(mesh N)*𝔞(unit p) with 𝔞(mesh N)*eW
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hBW hq) (positive_product _ _ hb hq)
    (by change Γ ⊢[PRAAx] le ((E*W*T+two*B*T+B*W)*(B*T)) ((residualCost N*T+B)*(B*W*T))
        dsimp only [residualCost,E,M]
        ipra_le 𝔞(B)*𝔞(T)^2*sl spare) main

theorem original_shifted_negative_gamma_location_residual_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (distanceBounded (ap2 nameF (var 1) (nameData (lower (var 0) (var 2)) (denominator (var 0) (var 2)) (var 2))) qzero
        (residualCost (var 2)*unit (var 1)+denominator (var 0) (var 2)) (denominator (var 0) (var 2)*unit (var 1))) :=
  closeUniv 3 (original_residual_at _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLocationResidual
