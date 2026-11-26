import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentCayleyRefinement
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentPartialQuadrature
import IPRADerivations.Analysis.Trigonometry.Arctangent.GaussianArctangentOriginalExponential

/-!
# The exact arctangent exponential at rational arguments

At A/B in the unit interval the regular arctangent name uses the
literal left-grid prefix for twice the imaginary arctangent. Its
original named exponential equals the Gaussian rational Cayley value.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentPartialExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentCayleyBudget (stage stage_ge)
open GaussianArctangentCayleyRefinement (rational_endpoint_estimate)
open GaussianArctangentCayleyValues (value numerator denominator)
open GaussianArctangentExponentialPrefix (prefixValue source prefix_bound)
open GaussianArctangentPartialQuadrature (nameF data mesh sample_at name_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRadiusExponentialName (input inputPrecision index)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianScalarExponentialProductTail (rectangleCutoff)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def exponentialF : PR 2 := GaussianRadiusExponentialName.nameF nameF
def exponentialData (A B : PTm n) : PTm n := GaussianRadiusExponentialName.data two (data A B)

private theorem mesh_lower (p : PTm n) : Γ ⊢[PRAAx] le (unit p) (mesh p) := by
  unfold mesh
  ipra_le 3*𝔞 (unit p)

private theorem mesh_two (p : PTm n) : Γ ⊢[PRAAx] le two (mesh p) :=
  le_congr (by ipra_ring) (.eqRefl _)
    (le_mul_mono (by ipra_le 2 : Γ ⊢[PRAAx] le two (num 4)) (unit_positive p))

theorem argument_bound (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data A B)) two one := by
  let M := B*mesh p
  let L := two*(M*M)
  let K := A*mesh p
  have hn := le_trans (le_succ_self one) (mesh_two (Γ := Γ) p)
  have hm := GaussianRationalHorner.positive_product B (mesh p) hB hn
  have hsrc : Γ ⊢[PRAAx] source M L := .andI hm (le_refl L)
  have hK : Γ ⊢[PRAAx] le K M := le_mul_mono hA (le_refl _)
  exact bound_congr (sample_at p A B).eqSymm (.eqRefl _) (.eqRefl _) (prefix_bound K M L hsrc hK)

theorem exponential_input (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] input nameF two (data A B) := by
  refine .andI (name_regular A B hB hA) (.allI ?_)
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hB.shift
  have ha : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hA.shift
  simpa [data,Syn.shift] using argument_bound (var 0) (Syn.shift A) (Syn.shift B) hb ha

theorem exponential_distance (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 exponentialF p (exponentialData A B)) (value B A) (num 130) (unit p) := by
  let j := inputPrecision two p
  let s := stage j (B*mesh j)
  let cutoff := rectangleCutoff two s
  have hpj : Γ ⊢[PRAAx] le p j := le_trans (le_add_right _ _) (le_add_right _ _)
  have hs : Γ ⊢[PRAAx] le p s := le_trans hpj (stage_ge j (B*mesh j))
  have hk : Γ ⊢[PRAAx] le (index two p) cutoff :=
    GaussianExponentialReference.index_below_rectangle two two _ _ (le_add_right _ _) hs
  have h := exponential_input A B hB hA
  have hprogram := GaussianExponentialReference.finite_reference nameF two (data A B) p j cutoff h (le_refl _) hk
  have htarget := distance_congr
    (GaussianNameConjugation.scalar_sum_congr cutoff (sample_at j A B)).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (rational_endpoint_estimate A B (mesh j) j hB hA (mesh_two j) (mesh_lower j))
  have hcoarse := GaussianExponentialReference.dyadic_weaken _ _ _ _ _ hpj htarget
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p)
      (distance_symmetric _ _ _ _ (unit_positive p) hprogram) hcoarse)

theorem exponential_cross (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] crossEquivalent exponentialF constantF (exponentialData A B) (value B A) := by
  apply GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ (num 130)
    (GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input A B hB hA)) (constant_regular _)
  refine .allI ?_
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hB.shift
  have ha : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hA.shift
  have hd := exponential_distance (var 0) (Syn.shift A) (Syn.shift B) hb ha
  simpa [GaussianNamedDiagonalRate.diagonalRate,exponentialF,exponentialData,data,value,numerator,denominator,two,
    Syn.shift] using
    distance_congr (.eqRefl _) (constant_at (var 0) (value (Syn.shift B) (Syn.shift A))).eqSymm
      (.eqRefl _) (.eqRefl _) hd

theorem actual_rational_arctangent_Cayley_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ le (var 0) (var 1) ⟶
      crossEquivalent exponentialF constantF (exponentialData (var 0) (var 1)) (value (var 1) (var 0))) :=
  closeUniv 2 (.impI (.impI (exponential_cross _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentPartialExponential
