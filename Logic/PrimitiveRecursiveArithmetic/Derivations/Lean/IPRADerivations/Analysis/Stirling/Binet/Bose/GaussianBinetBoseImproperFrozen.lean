import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseImproperName
import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBosePrefixRefinementLate
import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseFrozenOriginCut

/-!
# The original improper Bose observation and retained frozen matrix

The improper observation, compact observation, literal refinement, and
frozen evaluation have separate clocks. The exact dyadic lower cutoff
and its physical width survive all the finite comparisons. The final
bound cuts the geometric tail before restoring the cells near zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseImproperFrozen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentQuadrature (fixedData)
open GaussianBinetBoseOriginExhaustion (cutoff width cutData cutoff_positive width_positive endpoint)
open GaussianBinetBoseFrozenSuffix (geometry fullMesh suffixValue)
open GaussianBinetBoseFrozenMatrix (errorCost)
open GaussianBinetBosePrefixQuadrature (cost)
open GaussianBinetSecondDecayFrozenTail (mesh)
open GaussianBinetSecondDecaySharedTail (clockFloor)
open GaussianBinetSecondDecayPiBridge (budget)
open GaussianBinetBoseImproperName (source nameF data)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (precision quadrature quadrature_index_congr)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "Compact" => GaussianBinetBoseCompact.nameF
local notation "Literal" => GaussianBinetBosePrefixQuadrature.evaluatorF

def baseMesh (s D T L : PTm n) : PTm n :=
  GaussianCompactRiemannName.mesh s (GaussianBinetBoseCompact.gain D (cutoff L) T) T

def refinementCost (D T L : PTm n) : PTm n := num 3*cutoff L+width T L*cost D T (cutoff L)
def freezingCost (K T L N : PTm n) : PTm n := width T L*(N*errorCost K T)
def alignmentCost (T L N : PTm n) : PTm n := width T L*(N*num 4)

theorem time_geometry (T L B : PTm n) (ht : Γ ⊢[PRAAx] le one T) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] geometry T (cutoff L) B (width T L) :=
  .andI (.andI ht (cutoff_positive L))
    (.andI (.andI hb (width_positive T L ht)) ((endpoint T L ht).eqSymm.eqTrans (mul_comm _ _)))

private theorem dyadic_fit (a b A D h : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (fits : Γ ⊢[PRAAx] le (A*unit h) D) (e : Γ ⊢[PRAAx] distanceBounded a b A D) :
    Γ ⊢[PRAAx] distanceBounded a b one (unit h) :=
  distance_radius_mono _ _ _ _ _ _ hD (unit_positive h)
    (le_congr (.eqRefl _) (one_mul D).eqSymm fits) e

theorem compact_window_error (h p s X Y D sign K T L : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign K) (ht : Γ ⊢[PRAAx] le one T)
    (hp : Γ ⊢[PRAAx] le h p) (hs : Γ ⊢[PRAAx] le h s)
    (far : Γ ⊢[PRAAx] le ((two*K)*unit h) T) (near : Γ ⊢[PRAAx] le (D*unit h) (cutoff L*(num 4*X))) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign K))
      (ap2 Compact s (cutData X Y D sign T L)) (num 4) (unit h) := by
  let V := cutoff L*(num 4*X)
  let J := T*V
  let A := (two*K)*V+D*T
  let U := unit h
  let P := unit p
  let S := unit s
  have hj : Γ ⊢[PRAAx] le one J := positive_product _ _ ht
    (positive_product _ _ (cutoff_positive L) (positive_product _ _ (by ipra_le 3) hz.andE₁.andE₁.andE₁))
  have up : Γ ⊢[PRAAx] le U P := GaussianExponentialReference.unit_monotone hp
  have us : Γ ⊢[PRAAx] le U S := GaussianExponentialReference.unit_monotone hs
  have far' : Γ ⊢[PRAAx] le ((two*K)*U) T := far
  have near' : Γ ⊢[PRAAx] le (D*U) V := near
  have fits : Γ ⊢[PRAAx] le (rateNumerator A J p s*U) (num 4*rateDenominator J p s) := by
    change Γ ⊢[PRAAx] le (((two*K*V+D*T)*P*S+(T*V)*(P+S))*U) (num 4*((T*V)*P*S))
    ipra_le 𝔞(V*P*S)*sl far'+𝔞(T*P*S)*sl near'+𝔞(T*V*S)*sl up+𝔞(T*V*P)*sl us
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive J p s hj) (unit_positive h) fits
    (rate_at nameF Compact (data X Y D sign K) (cutData X Y D sign T L) A J p s
      (GaussianBinetBoseImproperName.compact_rate X Y D sign K T L hz ht))

/-- Compare a genuine improper observation with the complete frozen matrix
at the retained cutoff. The two mesh counts are related by an exact
natural equality, and the remaining numerical hypotheses are separate
precision budgets for each source of error. -/
theorem observation_error (h p s u q k I r T L B R K X Y D sign : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign K) (ht : Γ ⊢[PRAAx] le one T)
    (hb : Γ ⊢[PRAAx] le one B) (hr : Γ ⊢[PRAAx] le one R) (hi : Γ ⊢[PRAAx] le one I)
    (counts : Γ ⊢[PRAAx] width T L*B ≐ R*baseMesh s D T L)
    (hp : Γ ⊢[PRAAx] le h p) (hs : Γ ⊢[PRAAx] le h s)
    (hu : Γ ⊢[PRAAx] le (precision s T) u) (hq : Γ ⊢[PRAAx] le u q)
    (live : Γ ⊢[PRAAx] le (cutoff L*cutoff L*unit s) (I+r))
    (freeze : Γ ⊢[PRAAx] le (budget (I+r) T*unit u) (unit k))
    (fine : Γ ⊢[PRAAx] le (mesh T (succ (I+r)) k) (fullMesh T (cutoff L) B))
    (later : Γ ⊢[PRAAx] le (clockFloor (fullMesh T (cutoff L) B) T (succ (I+r)) k) (unit q))
    (far : Γ ⊢[PRAAx] le ((two*K)*unit h) T) (origin : Γ ⊢[PRAAx] le (D*unit h) (cutoff L*(num 4*X)))
    (refineError : Γ ⊢[PRAAx] le (refinementCost D T L*unit h) (cutoff L*unit s))
    (freezeError : Γ ⊢[PRAAx] le (freezingCost K T L (I+r)*unit h) (cutoff L*unit u))
    (alignError : Γ ⊢[PRAAx] le (alignmentCost T L (I+r)*unit h) (cutoff L*unit q))
    (tailError : Γ ⊢[PRAAx] le ((num 11*K)*unit h) I) (prefixError : Γ ⊢[PRAAx] le ((I*(two*K))*unit h) (cutoff L*cutoff L)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign K))
      (GaussianBinetBoseFrozenMatrix.value q k I (fullMesh T (cutoff L) B) X Y D sign zero T one) (num 9) (unit h) := by
  let E := cutoff L
  let C := width T L
  let N := I+r
  let M := C*B
  let x := pairT N (fixedData X Y D sign)
  let w := ap2 nameF p (data X Y D sign K)
  let v := ap2 Compact s (cutData X Y D sign T L)
  let y := quadrature Literal u M (E+one) C E x
  let f := GaussianBinetBoseFrozenMatrix.value q k N M X Y D sign one C E
  let g := suffixValue q k N T E B C X Y D sign
  let z := GaussianBinetBoseFrozenMatrix.value q k I (fullMesh T E B) X Y D sign zero T one
  have geo := time_geometry T L B ht hb
  have panel := GaussianBinetBoseFrozenSuffix.strip_source T E B C X D sign geo hz.andE₁
  have he := geo.andE₁.andE₂
  have hm : Γ ⊢[PRAAx] le one M := positive_product _ _ geo.andE₂.andE₁.andE₂ hb
  have htarg := unit_positive (Γ := Γ) h
  have a : Γ ⊢[PRAAx] distanceBounded w v (num 4) (unit h) :=
    compact_window_error h p s X Y D sign K T L hz ht hp hs far origin
  have read := quadrature_index_congr Literal u (R*baseMesh s D T L) M (E+one) C E x counts.eqSymm
  have b : Γ ⊢[PRAAx] distanceBounded v y one (unit h) :=
    dyadic_fit _ _ _ _ h (positive_product _ _ he (unit_positive s)) refineError
      (distance_congr (.eqRefl _) read (.eqRefl _) (.eqRefl _)
        (GaussianBinetBosePrefixRefinementLate.refined_prefix_error s u R N X Y D sign T one C E panel hr hu live))
  have c : Γ ⊢[PRAAx] distanceBounded y f one (unit h) :=
    dyadic_fit _ _ _ _ h (positive_product _ _ he (unit_positive u)) freezeError
      (GaussianBinetBoseFrozenMatrix.quadrature_error u q k N M X Y D sign T K one C E panel hm hz.andE₂ hq freeze)
  have d : Γ ⊢[PRAAx] distanceBounded f g one (unit h) :=
    dyadic_fit _ _ _ _ h (positive_product _ _ he (unit_positive q)) alignError
      (GaussianBinetBoseFrozenSuffix.suffix_error q k N T E B C X Y D sign geo hz.andE₁)
  have clear : Γ ⊢[PRAAx] le (((num 11*K)*(E*E)+(I*(two*K))*I)*unit h) (two*(I*(E*E))) :=
    by ipra_le 𝔞(E*E)*sl tailError+𝔞(I)*sl prefixError
  have e : Γ ⊢[PRAAx] distanceBounded g z two (unit h) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hi (positive_product _ _ he he)) htarg clear
      (GaussianBinetBoseFrozenOriginCut.cut_and_restore q k I r T E B C K X Y D sign geo hz.andE₁ hi hz.andE₂ fine later)
  have first := distance_triangle_same _ _ _ _ _ _ htarg a b
  have middle := distance_triangle_same _ _ _ _ _ _ htarg c d
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ htarg (distance_triangle_same _ _ _ _ _ _ htarg first middle) e)

end LeanProofs.IPRA.Analysis.GaussianBinetBoseImproperFrozen
