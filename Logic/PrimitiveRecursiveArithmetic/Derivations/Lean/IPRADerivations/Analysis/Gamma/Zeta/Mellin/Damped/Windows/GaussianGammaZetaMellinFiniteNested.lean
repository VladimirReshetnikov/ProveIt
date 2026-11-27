import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.FiniteRows.GaussianGammaZetaMellinFiniteDampedModulus
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.EndpointBounds.GaussianGammaZetaMellinCutoffWindows

/-!
# Alignment of the finite damped compact Mellin names

Keep the same finite decay count and observation clock parameter
on both windows. Rescaling the earlier panel to the wider
denominator and changing its mesh gives the true middle panel.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteNested

open_ipra
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianGammaCompactCutoffGeometry
  (ratio ratio_positive lowerWidth middleWidth upperWidth lower_endpoint middle_endpoint
    widths_total eta_den_refinement three_endpoint)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive)
open GaussianGammaZetaMellinFiniteDampedEvaluator (evaluatorF)
open GaussianGammaZetaMellinFiniteDampedModulus (lipschitz original_sampled_modulus)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "nameF" => GaussianCompactRiemannName.nameF evaluatorF
local notation "cd" => GaussianCompactRiemannName.data
local notation "fd" => GaussianGammaZetaMellinFiniteDampedEvaluator.data
local notation "S" => GaussianEulerLowerPowerCoefficients.source

def data (z R B N Q a C E T : PTm n) : PTm n :=
  cd a C E (lipschitz N R E T) T (fd z B N Q)

def datum (z R B N Q A p : PTm n) : PTm n :=
  data (shifted z B) (R+one) B N Q one (width p A R) (etaDen p A R) (top p A R)

theorem interval_source (z R B A a C E T : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (ha : Γ ⊢[PRAAx] le one a) (he : Γ ⊢[PRAAx] le one E)
    (ht : Γ ⊢[PRAAx] le (a+C) (E*T)) :
    Γ ⊢[PRAAx] intervalSource (shifted z B) (R+one) B a C E T :=
  .andI (.andI hz.andE₂.andE₁.andE₁ (.andI he
    (GaussianGammaEulerShiftLimit.shifted_bound z R B hz.andE₂.andE₁.andE₂))) (.andI ha ht)

theorem compact_input (z R B N Q a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hQ : Γ ⊢[PRAAx] le N Q) :
    Γ ⊢[PRAAx] GaussianCompactRiemannName.input evaluatorF a C E (lipschitz N R E T) T (fd z B N Q) :=
  .andI h.andE₂.andE₁ (.andI h.andE₁.andE₂.andE₁
    (.andI (le_trans (le_add_left C a) h.andE₂.andE₂) (original_sampled_modulus _ _ _ _ _ _ _ _ _ h hQ)))

theorem cutoff_source (z R B A p : PTm n) (hz : Γ ⊢[PRAAx] S z R B A) :
    Γ ⊢[PRAAx] intervalSource (shifted z B) (R+one) B one (width p A R) (etaDen p A R) (top p A R) :=
  interval_source z R B A _ _ _ _ hz (le_refl one) (eta_den_positive p A R)
    (le_congr (exact_right_endpoint p A R).eqSymm (.eqRefl _) (le_refl _))

theorem regular (z R B N Q A p : PTm n) (hz : Γ ⊢[PRAAx] S z R B A) (hQ : Γ ⊢[PRAAx] le N Q) :
    Γ ⊢[PRAAx] pointCN nameF (datum z R B N Q A p) :=
  GaussianCompactRiemannName.name_regular _ _ _ _ _ _ _ (compact_input _ _ _ _ _ _ _ _ _ (cutoff_source z R B A p hz) hQ)

theorem middle_alignment (z R B N Q A p q : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hQ : Γ ⊢[PRAAx] le N Q) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (datum z R B N Q A p)
      (data (shifted z B) (R+one) B N Q (one+lowerWidth p q A) (middleWidth p q A R) (etaDen q A R) (top q A R)) := by
  let E₀ := etaDen p A R
  let T₀ := top p A R
  let W := width p A R
  let E := etaDen q A R
  let T := top q A R
  let C₁ := lowerWidth p q A
  let C₂ := middleWidth p q A R
  let L₀ := lipschitz N (R+one) E₀ T₀
  let L := lipschitz N (R+one) E T
  let K := ratio p q A
  let x := fd (shifted z B) B N Q
  have old := compact_input _ _ _ _ _ _ _ _ _ (cutoff_source z R B A p hz) hQ
  have si : Γ ⊢[PRAAx] GaussianCompactIntervalRescaling.input evaluatorF K one W E₀ L₀ T₀ x :=
    .andI (ratio_positive p q A) old
  have scale := GaussianCompactIntervalRescaling.name_rescaling evaluatorF K one W E₀ L₀ T₀ x si
  have aEq : Γ ⊢[PRAAx] K*one ≐ one+C₁ :=
    ((mul_comm _ _).eqTrans (one_mul _)).eqTrans (lower_endpoint p q A).eqSymm
  have eEq : Γ ⊢[PRAAx] K*E₀ ≐ E := (eta_den_refinement p q A R hpq).eqSymm
  have dEq := GaussianGammaZetaMellinCutoffWindows.data_congr (K*one) (one+C₁) (K*W) C₂ (K*E₀) E L₀ T₀ x
    aEq (.eqRefl _) eEq
  have adjusted := GaussianGammaCompactCutoffAlignment.cross_data_congr nameF nameF _ _ _ _
    (.eqRefl _) dEq scale
  have edge : Γ ⊢[PRAAx] (one+C₁)+C₂ ≐ E*T₀ :=
    (congrAdd (lower_endpoint p q A) (.eqRefl _)).eqTrans (middle_endpoint p q A R hpq)
  have upper : Γ ⊢[PRAAx] le ((one+C₁)+C₂) (E*T) :=
    le_congr ((mul_comm T₀ E).eqTrans edge.eqSymm) (mul_comm T E)
      (mul_le_mul_right E (GaussianGammaCompactCutoffGeometry.top_monotone p q A R hpq))
  have fresh := compact_input _ _ _ _ _ _ _ _ _
    (interval_source z R B A _ _ _ _ hz (le_add_right _ _) (eta_den_positive q A R) upper) hQ
  have moved := GaussianCompactIntervalRescaling.scaled_input evaluatorF K one W E₀ L₀ T₀ x si
  have aligned : Γ ⊢[PRAAx] GaussianCompactRiemannName.input evaluatorF (one+C₁) C₂ E L₀ T₀ x := by
    have eq := Prf.eqSubst (Ax := PRAAx) (Γ := Γ)
      (GaussianCompactRiemannName.input evaluatorF (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : Fm PTm 6)
      ![K*one,K*W,K*E₀,L₀,T₀,x] ![one+C₁,C₂,E,L₀,T₀,x]
      (fun i => by fin_cases i; exact aEq; exact .eqRefl _; exact eEq; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _)
      (by simpa [Matrix.cons_val] using moved)
    simpa [Matrix.cons_val] using eq
  exact cross_trans _ _ _ _ _ _ adjusted
    (GaussianCompactMeshIndependence.name_independence evaluatorF _ _ _ L₀ T₀ L T x (.andI aligned fresh))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteNested
