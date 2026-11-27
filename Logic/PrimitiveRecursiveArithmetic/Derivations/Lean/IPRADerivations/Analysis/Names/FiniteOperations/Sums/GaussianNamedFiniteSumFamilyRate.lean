import IPRADerivations.Analysis.Names.FiniteOperations.Sums.Families.GaussianNamedFiniteSumFamilyCongruence
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

/-!
# Uniform variation of actual finite named sums

A uniform independent rate for each row gives the rate for the original
named sum, multiplied by the internal length. The original row precision
pays for the accumulated observation errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamilyRate

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianFastValueCut (exponent query_budget)
open GaussianNamedFiniteSumFamily (body data finite nameF sample_at term_at)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def rows (f g : PR 2) (t u : PTm 2) (N x y H D : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶ independentRate f g (inst2 t (var 0) (Syn.shift x))
    (inst2 u (var 0) (Syn.shift y)) (Syn.shift H) (Syn.shift D))

ipra_subst rows [Syn.subst_shift, Syn.shift_subst]

theorem row_at (f g : PR 2) (t u : PTm 2) (N x y H D i : PTm n)
    (h : Γ ⊢[PRAAx] rows f g t u N x y H D) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] independentRate f g (inst2 t i x) (inst2 u i y) H D := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ independentRate f g (inst2 t i x) (inst2 u i y) H D := by
    simpa [rows] using h.allE i
  exact rule.impE hi

theorem finite_rate (f g : PR 2) (t u : PTm 2) (p q N x y H D : PTm n)
    (hd : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] rows f g t u N x y H D) :
    Γ ⊢[PRAAx] distanceBounded (finite f t p N x) (finite g u q N y)
      (N*rateNumerator H D p q) (rateDenominator D p q) := by
  have each : Γ ⊢[PRAAx] termsDistance (body f t) (body g u) N (pairT p x) (pairT q y)
      (rateNumerator H D p q) (rateDenominator D p q) := by
    refine .allI (.impI ?_)
    let sh (a : PTm n) := Syn.shift a
    let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] rows f g t u (sh N) (sh x) (sh y) (sh H) (sh D) := by
      simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
    have e := rate_at f g _ _ (sh H) (sh D) (sh p) (sh q)
      (row_at f g t u (sh N) (sh x) (sh y) (sh H) (sh D) (var 0) hs Prf.hyp0)
    simpa only [Syn.shift,sh,Δ,subst_pairT,GaussianNamedInverseRate.subst_rateNumerator,
      GaussianNamedInverseRate.subst_rateDenominator] using
      distance_congr (term_at f t (var 0) (sh p) (sh x)).eqSymm
        (term_at g u (var 0) (sh q) (sh y)).eqSymm (.eqRefl _) (.eqRefl _) e
  exact sum_distance _ _ N _ _ _ _ (denominator_positive D p q hd) each

theorem original_observations (f g : PR 2) (t u : PTm 2) (p q N x y H D : PTm n)
    (hd : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] rows f g t u N x y H D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f t) p (data N x)) (ap2 (nameF g u) q (data N y))
      (rateNumerator (N*H) D p q) (rateDenominator D p q) := by
  let k := exponent N p
  let l := exponent N q
  have first := query_budget (Γ := Γ) N p
  have second := query_budget (Γ := Γ) N q
  have raw := finite_rate f g t u k l N x y H D hd h
  have narrow := distance_radius_mono _ _ _ _ (rateNumerator (N*H) D p q) (rateDenominator D p q)
    (denominator_positive D k l hd) (denominator_positive D p q hd)
    (by
      dsimp only [rateNumerator,rateDenominator]
      ipra_le (𝔞 D)^2*𝔞(unit q)*𝔞(unit l)*sl first + (𝔞 D)^2*𝔞(unit p)*𝔞(unit k)*sl second) raw
  exact distance_congr (sample_at f t p N x).eqSymm (sample_at g u q N y).eqSymm (.eqRefl _) (.eqRefl _) narrow

theorem original_rate (f g : PR 2) (t u : PTm 2) (N x y H D : PTm n)
    (hd : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] rows f g t u N x y H D) :
    Γ ⊢[PRAAx] independentRate (nameF f t) (nameF g u) (data N x) (data N y) (N*H) D := by
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] rows f g t u (sh N) (sh x) (sh y) (sh H) (sh D) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  have hd' : Δ ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hd.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Syn.shift,sh,GaussianNamedFiniteSumFamily.subst_data,PTm.subst_mul] using
    original_observations f g t u (var 1) (var 0) (sh N) (sh x) (sh y) (sh H) (sh D) hd' hs

theorem actual_original_finite_sum_family_rate_closed (f g : PR 2) (t u : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((le one (var 4) ⋏ rows f g t u (var 0) (var 1) (var 2) (var 3) (var 4)) ⟶
        independentRate (nameF f t) (nameF g u) (data (var 0) (var 1)) (data (var 0) (var 2))
          (var 0*var 3) (var 4)) :=
  closeUniv 5 (.impI (original_rate f g t u _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteSumFamilyRate
