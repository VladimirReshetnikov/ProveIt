import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetStirlingVerticalGrid
import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetStirlingRescale
import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetStirlingRealBound
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateComposition
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# Sharp vertical comparison and the complex Stirling remainder bound

Choose an internal subdivision and a sufficiently late common observation
clock. The quadratic grid remainder and the sum of clock errors vanish
with this explicit schedule. Rescaling identifies the grid endpoints
with the original charts, including the real-axis endpoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBinetStirlingVerticalBound

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetStirlingRemainder (nameF data subst_data regular)
open GaussianBinetStirlingVerticalGrid
  (sample rowNumerator rowDenominator grid_distance mesh_positive row_denominator_positive requiredMesh offsetRadius)
open GaussianBinetStirlingVerticalRate (quadraticCost leadingNumerator leadingDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameEquivalence (cross_at cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (distanceBounded)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem diagonal (p A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B D sign x)) (ap2 nameF p (data A zero D sign x))
      (diagonalNumerator (num 3*B) (two*A) (num 6) p) (diagonalDenominator (two*A) p) := by
  let U := unit p
  let C := quadraticCost D (offsetRadius A B)
  let M := requiredMesh A B D+(C*(B*B)+one)*U
  let r := GaussianFastValueCut.exponent (two*M) p
  let V := unit r
  let P := two*A
  let Q := P*U
  let a := ap2 nameF p (data A B D sign x)
  let b := ap2 nameF p (data A zero D sign x)
  let c := sample r A B D sign x M M
  let d := sample r A B D sign x M zero
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) r
  have hm : Γ ⊢[PRAAx] le (requiredMesh A B D) M := le_add_right _ _
  have hM := mesh_positive A B D M hm
  have hD := h.andE₂
  have hDD := positive_product D D hD hD
  have hP := positive_product two A (le_succ_self one) h.andE₁.andE₁
  have hQ := positive_product P U hP hu
  have huv := positive_product U V hu hv
  have hNV := row_denominator_positive r A B D sign M h hm
  have paid : Γ ⊢[PRAAx] le (C*(B*B)*U) M := by
    dsimp only [M]
    ipra_le 𝔞(requiredMesh A B D)+𝔞(U)
  have pmesh : Γ ⊢[PRAAx] le (C*(B*B)*U) (M*(D*D)) :=
    le_trans paid (by ipra_le 𝔞(M)*sl hDD)
  have pclock : Γ ⊢[PRAAx] le (two*M*U) V := GaussianFastValueCut.query_budget (two*M) p
  have grow : Γ ⊢[PRAAx] le U V :=
    le_trans (by ipra_le (2*sl hM+1)*𝔞(U)) pclock
  have grid := grid_distance r A B D sign x M h hm
  have sum : Γ ⊢[PRAAx] distanceBounded c d (num 3*B*U+two*P) Q := by
    apply distance_radius_mono _ _ _ _ _ _ hNV hQ ?_ grid
    dsimp only [rowNumerator,rowDenominator,leadingNumerator,leadingDenominator,P]
    change Γ ⊢[PRAAx] le (((num 3*B*((M*D)*(M*D))+C*(B*B)*(two*(M*A)))*V+
      two*(two*(M*A)*((M*D)*(M*D))))*M*(two*A*U))
      ((num 3*B*U+two*(two*A))*(two*(M*A)*((M*D)*(M*D))*V))
    ipra_le 4*𝔞(M)^2*𝔞(A)^2*𝔞(V)*sl pmesh+2*𝔞(A)*𝔞(two*(M*A)*((M*D)*(M*D)))*sl pclock
  have back := GaussianBinetStirlingRescale.rescale A B D sign x M h hM
  have init := GaussianBinetStirlingRescale.rescale A zero D sign x M h hM
  have e0 : Γ ⊢[PRAAx] data (M*A) (zero*B) (M*D) sign x ≐ data (M*A) (M*zero) (M*D) sign x := by
    have e : Γ ⊢[PRAAx] zero*B ≐ M*zero := by ipra_ring
    simpa only [subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (data (Syn.shift (M*A)) (var 0) (Syn.shift (M*D)) (Syn.shift sign) (Syn.shift x)) e
  have first : Γ ⊢[PRAAx] distanceBounded a c (two*P) Q :=
    distance_radius_mono _ _ _ _ _ _ huv hQ (by dsimp only [Q]; ipra_le 𝔞(P)*𝔞(U)*sl grow)
      (cross_at nameF nameF _ _ p r (cross_symm _ _ _ _ back))
  have last : Γ ⊢[PRAAx] distanceBounded d b (two*P) Q :=
    distance_radius_mono _ _ _ _ _ _ (positive_product V U hv hu) hQ
      (by dsimp only [Q]; ipra_le 𝔞(P)*𝔞(U)*sl grow)
      (distance_congr (congrAp2 nameF (.eqRefl r) e0).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (cross_at nameF nameF _ _ r p init))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [diagonalNumerator,P,U]; ipra_ring) (.eqRefl _)
    (distance_triangle_same a d b _ _ Q hQ (distance_triangle_same a c d _ _ Q hQ first sum) last)

theorem vertical_rate (A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data A B D sign x) (data A zero D sign x) (num 3*B) (two*A) := by
  apply GaussianNamedLipschitzRate.independent_rate nameF nameF _ _ _ _ (num 6)
    (positive_product two A (le_succ_self one) h.andE₁.andE₁) (regular A B D sign x h) (regular A zero D sign x h)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s D) (s sign) :=
    by simpa [s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift
  simpa only [diagonalEnvelope,s,Syn.shift,subst_data,PTm.subst_mul,PTm.subst_num,two,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using diagonal (var 0) (s A) (s B) (s D) (s sign) (s x) hs

theorem remainder_rate (A B D sign x : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data A B D sign x) qzero (D+num 18*B) (num 12*A) := by
  let t : PTm n := num 12*A
  have ha := h.andE₁.andE₁
  have h1 := positive_product two A (le_succ_self one) ha
  have h2 : Γ ⊢[PRAAx] le one t := positive_product (num 12) A (by ipra_le 11) ha
  have raw := GaussianNamedRateComposition.compose nameF nameF constantF
    (data A B D sign x) (data A zero D sign x) qzero (num 3*B) (two*A) D t h1 h2
      (vertical_rate A B D sign x h) (GaussianBinetStirlingRealBound.axis_rate A D sign x h)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ h1 h2) h2
    (by dsimp only [GaussianNamedRateComposition.leadingNumerator,GaussianNamedRateComposition.leadingDenominator,t]; ipra_le 0) raw

theorem actual_complex_Stirling_vertical_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 2) (var 3) ⟶ independentRate nameF nameF
      (data (var 0) (var 1) (var 2) (var 3) (var 4)) (data (var 0) zero (var 2) (var 3) (var 4))
        (num 3*var 1) (two*var 0)) :=
  closeUniv 5 (.impI (vertical_rate _ _ _ _ _ Prf.hyp0))

theorem actual_complex_Stirling_remainder_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 2) (var 3) ⟶ independentRate nameF constantF
      (data (var 0) (var 1) (var 2) (var 3) (var 4)) qzero (var 2+num 18*var 1) (num 12*var 0)) :=
  closeUniv 5 (.impI (remainder_rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetStirlingVerticalBound
