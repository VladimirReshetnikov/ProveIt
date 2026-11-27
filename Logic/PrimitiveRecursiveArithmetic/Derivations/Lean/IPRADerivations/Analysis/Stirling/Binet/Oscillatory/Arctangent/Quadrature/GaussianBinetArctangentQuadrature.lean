import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.Arctangent.Resolvents.GaussianBinetArctangentResolventRate
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStrip

/-!
# The original compact quadrature defining the right-half-plane arctangent

Integrate the exact rational resolvent from zero to the encoded rational
time. A unit translation of the tags gives the positive tag format
required by the checked compact quadrature, while the integrand uses
the unshifted coordinate.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetArctangentQuadrature

open_ipra
open GaussianBinetArctangentResolvent (value)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianCompactRiemannName (inside nameData evaluatorName localBody sampledModulus)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def fixedData (X Y D sign : PTm n) : PTm n := pairT X (pairT Y (pairT D sign))
def evaluatorTerm (t x : PTm n) : PTm n :=
  value (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x))) (sndT (sndT (sndT x))) (tagNumerator t) (sndT t)
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 1) (var 2) : PTm 3)
abbrev nameF : PR 2 := GaussianCompactRiemannName.nameF evaluatorF
def data (X Y D sign A B : PTm n) : PTm n :=
  GaussianCompactRiemannName.data (B+zero) A B (D*D) A (fixedData X Y D sign)

ipra_subst fixedData

ipra_subst evaluatorTerm

ipra_subst data

theorem evaluator_at (p t X Y D sign : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p t (fixedData X Y D sign) ≐ value X Y D sign (tagNumerator t) (sndT t) := by
  have read := toPR_pairVector3_eq (Γ := Γ) (k := 3)
    (value (var 2) (var 3) (var 4) (var 5) (tagNumerator (var 1)) (sndT (var 1))) p t ![X, Y, D, sign]
  simp only [GaussianBinetArctangentResolvent.subst_value,
    GaussianBinetLaplaceStrip.subst_tagNumerator, subst_sndT, Syn.subst_var] at read
  exact read

theorem wrapped_at (p t X Y D sign : PTm n) : Γ ⊢[PRAAx]
    ap2 (evaluatorName evaluatorF) p (nameData t (fixedData X Y D sign)) ≐ value X Y D sign (tagNumerator t) (sndT t) :=
  (GaussianCompactRiemannName.evaluator_at evaluatorF p t _).eqTrans (evaluator_at p t X Y D sign)

private theorem local_observations (X Y D sign A B t u M H p q : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H)
    (ht : Γ ⊢[PRAAx] inside (B+zero) A B t) (hu : Γ ⊢[PRAAx] inside (B+zero) A B u)
    (h : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) M H) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (evaluatorName evaluatorF) p (nameData t (fixedData X Y D sign)))
      (ap2 (evaluatorName evaluatorF) q (nameData u (fixedData X Y D sign)))
      (rateNumerator (D*D*M) H p q) (rateDenominator H p q) := by
  have hT : Γ ⊢[PRAAx] le (zero+A) (B*A) := by ipra_le 𝔞 A*sl hB
  have tags := GaussianBinetLaplaceStrip.tag_source t u zero A B A M H hB hT hH ht hu h
  have hx := positive_product _ _ hz.andE₁.andE₁ hz.andE₁.andE₁
  have raw := GaussianBinetArctangentResolventRate.time_distance X Y D sign (tagNumerator t) (sndT t)
    (tagNumerator u) (sndT u) M H hz tags.andE₁ tags.andE₂.andE₁ hH tags.andE₂.andE₂.andE₂.andE₂.andE₂
  have narrow := distance_radius_mono _ _ _ _ (D*D*M) H (positive_product _ _ hx hH) hH
    (by ipra_le 𝔞 D^2*𝔞 M*𝔞 H*sl hx) raw
  have widened := distance_radius_mono _ _ _ _ (rateNumerator (D*D*M) H p q) (rateDenominator H p q)
    hH (denominator_positive H p q hH)
    (le_of_eq_add (d := H*H*(unit p+unit q)) (by dsimp only [rateNumerator,rateDenominator]; ipra_ring)) narrow
  exact distance_congr (wrapped_at p t X Y D sign).eqSymm (wrapped_at q u X Y D sign).eqSymm (.eqRefl _) (.eqRefl _) widened

theorem local_rate (X Y D sign A B t u M H : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hB : Γ ⊢[PRAAx] le one B) (hH : Γ ⊢[PRAAx] le one H)
    (ht : Γ ⊢[PRAAx] inside (B+zero) A B t) (hu : Γ ⊢[PRAAx] inside (B+zero) A B u)
    (h : Γ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value t) (GaussianCompactRiemannName.value u) M H) :
    Γ ⊢[PRAAx] independentRate (evaluatorName evaluatorF) (evaluatorName evaluatorF)
      (nameData t (fixedData X Y D sign)) (nameData u (fixedData X Y D sign)) (D*D*M) H := by
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have zs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
    simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift.shift
  have bs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hB.shift.shift
  have hs : Δ ⊢[PRAAx] le one (s H) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hH.shift.shift
  have ts : Δ ⊢[PRAAx] inside (s B+zero) (s A) (s B) (s t) := by simpa [Δ,s,Fm.shift,Syn.shift] using ht.shift.shift
  have us : Δ ⊢[PRAAx] inside (s B+zero) (s A) (s B) (s u) := by simpa [Δ,s,Fm.shift,Syn.shift] using hu.shift.shift
  have ds : Δ ⊢[PRAAx] distanceBounded (GaussianCompactRiemannName.value (s t)) (GaussianCompactRiemannName.value (s u)) (s M) (s H) :=
    by simpa [Δ,s,Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Δ,s,Syn.shift,GaussianCompactRiemannName.subst_nameData,subst_fixedData,PTm.subst_mul] using
    local_observations (s X) (s Y) (s D) (s sign) (s A) (s B) (s t) (s u) (s M) (s H) (var 1) (var 0) zs bs hs ts us ds

theorem sampled_modulus (X Y D sign A B : PTm n) (hz : Γ ⊢[PRAAx] source X D sign) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] sampledModulus evaluatorF (B+zero) A B (D*D) (fixedData X Y D sign) := by
  let s (z : PTm n) := Syn.shift (Syn.shift (Syn.shift (Syn.shift z)))
  let Δ := (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift
  have zs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) := by
    simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source,Function.comp_def] using
      hz.shift.shift.shift.shift
  have bs : Δ ⊢[PRAAx] le one (s B) := by
    simpa [Δ,s,Fm.shift,Syn.shift,one,Function.comp_def] using hB.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI (.impI ?_)))))))
  simpa only [localBody,Syn.shift,s,subst_fixedData,PTm.subst_add,PTm.subst_mul,ConciseIPRA.PTm.subst_zero,Δ] using
    local_rate (s X) (s Y) (s D) (s sign) (s A) (s B) (var 3) (var 2) (var 1) (var 0)
      zs.wk.wk.wk.wk bs.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem compact_input (X Y D sign A B : PTm n) (hz : Γ ⊢[PRAAx] source X D sign) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] GaussianCompactRiemannName.input evaluatorF (B+zero) A B (D*D) A (fixedData X Y D sign) :=
  .andI (le_trans hB (le_add_right _ _)) (.andI hB (.andI (by ipra_le 𝔞 A*sl hB) (sampled_modulus X Y D sign A B hz hB)))

theorem regular (X Y D sign A B : PTm n) (hz : Γ ⊢[PRAAx] source X D sign) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN nameF (data X Y D sign A B) :=
  GaussianCompactRiemannName.name_regular _ _ _ _ _ _ _ (compact_input X Y D sign A B hz hB)

theorem actual_Binet_right_half_plane_arctangent_quadrature_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 0) (var 2) (var 3) ⋏ le one (var 5)) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (regular _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetArctangentQuadrature
