import IPRADerivations.Analysis.GaussianBinetOscillatorySineRectangle

/-!
# The original arctangent name and the finite damped sine integral

Compose the two actual rectangle comparisons, and compare any exact
refinement of the arctangent name's own observation mesh. The bounds
retain the finite damping horizon, cutoff, and sampling errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetArctangentSineGridComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentQuadrature (evaluatorF fixedData nameF data)
open GaussianBinetArctangentCosineLaplace (error)
open GaussianBinetOscillatorySineRows (numeratorBound)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature mesh mesh_positive precision)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Sine" => GaussianBinetOscillatorySineRectangle.value

def cosineDenominator (p B L : PTm n) : PTm n := B*(unit p*unit L)
def sineDenominator (p B M N : PTm n) : PTm n := (B*M)*unit (p+N)
def combinedDenominator (p B M L N : PTm n) : PTm n := cosineDenominator p B L*sineDenominator p B M N

def combinedNumerator (p M D A B R U K L N : PTm n) : PTm n :=
  (A*error p R U K (D*L) L)*sineDenominator p B M N+
    ((D*L)*numeratorBound p M D A B U L N)*cosineDenominator p B L

private theorem cosine_den_positive (p B L : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (cosineDenominator p B L) := positive_product _ _ hB (positive_product _ _ (unit_positive p) (unit_positive L))
private theorem sine_den_positive (p B M N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (sineDenominator p B M N) := positive_product _ _ (positive_product _ _ hB hM) (unit_positive _)

theorem quadrature_error (p q M X Y D sign A B R U K L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M)
    (hA : Γ ⊢[PRAAx] le A (B*U)) (hm : Γ ⊢[PRAAx] le D (K*X)) (hL : Γ ⊢[PRAAx] le one L) (hLp : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+U)*(D*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N)
    (hC : Γ ⊢[PRAAx] le (U*(D*L)) M) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF q M (B+zero) A B (fixedData X Y D sign))
      (Sine p X Y D sign A B R U L N) (combinedNumerator p M D A B R U K L N) (combinedDenominator p B M L N) := by
  have den₁ := cosine_den_positive p B L hB
  have den₂ := sine_den_positive p B M N hB hM
  have first := distance_symmetric _ _ _ _ den₁
    (GaussianBinetArctangentCosineRectangle.rectangle_error p q M X Y D sign A B R U K L N hz hB hM hA hm hLp hN hpN)
  have last := GaussianBinetOscillatorySineRectangle.rectangle_error p M X Y D sign A B R U L N hz hB hM
    (le_trans (unit_positive p) hpN) hL hA hC
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ den₁ den₂ first last

def refinementDenominator (q A B D : PTm n) : PTm n :=
  B*rateDenominator (B*mesh q (D*D) A) (precision q A) (precision q A)
def refinementNumerator (q A B D : PTm n) : PTm n :=
  A*rateNumerator ((D*D)*A) (B*mesh q (D*D) A) (precision q A) (precision q A)

theorem original_sample_error (p q refinement X Y D sign A B R U K L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B) (href : Γ ⊢[PRAAx] le one refinement)
    (hA : Γ ⊢[PRAAx] le A (B*U)) (hm : Γ ⊢[PRAAx] le D (K*X)) (hL : Γ ⊢[PRAAx] le one L) (hLp : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+U)*(D*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N)
    (hC : Γ ⊢[PRAAx] le (U*(D*L)) (refinement*mesh q (D*D) A)) :
    let M := refinement*mesh q (D*D) A
    let V := combinedDenominator p B M L N
    let W := refinementDenominator q A B D
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF q (data X Y D sign A B))
      (Sine p X Y D sign A B R U L N)
      (refinementNumerator q A B D*V+combinedNumerator p M D A B R U K L N*W) (W*V) := by
  let m := mesh q (D*D) A
  let M := refinement*m
  let s := precision q A
  let x := fixedData X Y D sign
  let E := B*m
  let V := combinedDenominator p B M L N
  let W := refinementDenominator q A B D
  let u := ap2 nameF q (data X Y D sign A B)
  let v := quadrature evaluatorF s M (B+zero) A B x
  have h₀ := mesh_positive (Γ := Γ) q (D*D) A
  have hM := positive_product _ _ href h₀
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hB h₀
  have hW : Γ ⊢[PRAAx] le one W := positive_product _ _ hB (denominator_positive E s s hE)
  have hV : Γ ⊢[PRAAx] le one V := positive_product _ _ (cosine_den_positive p B L hB) (sine_den_positive p B M N hB hM)
  have raw := GaussianCompactRiemannName.quadrature_refinement evaluatorF s s m refinement (B+zero) A B (D*D) x
    (le_trans hB (le_add_right _ _)) hB h₀ href (GaussianBinetArctangentQuadrature.sampled_modulus X Y D sign A B hz.andE₁ hB)
  have offset := GaussianCompactRiemannName.name_at (Γ := Γ) evaluatorF q (B+zero) A B (D*D) A x
  have first : Γ ⊢[PRAAx] distanceBounded u v (refinementNumerator q A B D) W :=
    distance_congr offset.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (distance_symmetric _ _ _ _ hW raw)
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hW hV first
    (quadrature_error p s M X Y D sign A B R U K L N hz hB hM hA hm hL hLp hN hpN hC)

end LeanProofs.IPRA.Analysis.GaussianBinetArctangentSineGridComparison
