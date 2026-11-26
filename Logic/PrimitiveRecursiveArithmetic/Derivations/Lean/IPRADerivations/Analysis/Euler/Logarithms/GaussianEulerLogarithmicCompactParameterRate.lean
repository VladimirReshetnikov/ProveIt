import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicCompactTaylor
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicCompactBound

/-!
# Fixed-interval parameter rate for the original logarithmic compact names

The proved quadratic Taylor error and the actual compact absolute bound
give a linear parameter estimate on the original small-increment domain.
Both requested compact observations remain independent.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCompactParameterRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicTaylorGrid (source)
open GaussianEulerLogarithmicCompactTaylor (point actualLinear parameter_bound shifted_source)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianEulerLogarithmicParameterIncrement (curvature)
open GaussianEulerLogarithmicMultiplier (majorant logRadius)
open GaussianEulerLogarithmicIntervalName (nameF data name_regular)
open GaussianRationalHorner (qadd qmul ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def gain (j R C E T X : PTm n) : PTm n := C*(curvature j R E T+majorant (succ j) R E T)*X
def scaleDenominator (E Y : PTm n) : PTm n := E*Y
def numerator (p q j R C E T X Y : PTm n) : PTm n :=
  GaussianNamedInverseRate.rateNumerator (gain j R C E T X) (scaleDenominator E Y) p q
def denominator (p q E Y : PTm n) : PTm n := GaussianNamedInverseRate.rateDenominator (scaleDenominator E Y) p q

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (j R C E T X : PTm n) :
    Syn.subst σ (gain j R C E T X) = gain (Syn.subst σ j) (Syn.subst σ R) (Syn.subst σ C)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ X) := by simp [gain]
@[simp] theorem subst_scaleDenominator {m : ℕ} (σ : Fin n → PTm m) (E Y : PTm n) :
    Syn.subst σ (scaleDenominator E Y) = scaleDenominator (Syn.subst σ E) (Syn.subst σ Y) := by simp [scaleDenominator]

theorem increment_radius_small (z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx] le X Y := by
  have jpos : Γ ⊢[PRAAx] le one (logRadius E T) :=
    le_of_eq_add (d := E*(T+one)+num 24) (by unfold logRadius GaussianCompactLogarithmBounds.radius; ipra_ring)
  exact le_trans (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right X jpos)) hs.andE₂.andE₂.andE₂.andE₁

theorem linear_term_bound (p j z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (actualLinear p p j z R B a C E T h D) (point p j z R B a C E T)
      (C*majorant (succ j) R E T*X) (E*Y) := by
  have product := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hs.andE₂.andE₂.andE₁ hs.andE₁.andE₁.andE₂.andE₁
    hs.andE₂.andE₂.andE₂.andE₂ (GaussianEulerLogarithmicCompactBound.original_compact_bound p (succ j) z R B a C E T hs.andE₁)
  have canonical := GaussianRationalHorner.qmul_canonical (Γ := Γ) (ofGaussian h D) (point p (succ j) z R B a C E T)
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRationalSyntheticDivision.qadd_sub_cancel (point p j z R B a C E T) _ canonical).eqSymm
    (by ipra_ring) (by ipra_ring) product

theorem original_diagonal (p j z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (point p j (shifted z B h D) (R+one) (B*D) a C E T) (point p j z R B a C E T)
      (gain j R C E T X*unit p+num 12*scaleDenominator E Y) (scaleDenominator E Y*unit p) := by
  let V := unit p
  let K := curvature j R E T
  let L := majorant (succ j) R E T
  let DD := scaleDenominator E Y*V
  have hy := hs.andE₂.andE₂.andE₁
  have he := hs.andE₁.andE₁.andE₂.andE₁
  have ey := positive_product _ _ he hy
  have den : Γ ⊢[PRAAx] le one DD := positive_product _ _ ey (unit_positive p)
  have oldDen := positive_product _ _ (GaussianEulerLogarithmicCompactTaylor.quadratic_denominator_positive E Y he hy) (unit_positive p)
  have small := increment_radius_small z R B a C E T h D X Y hs
  have firstNative : Γ ⊢[PRAAx]
      le ((C*K*X*X*V+num 12*(E*(Y*Y)))*DD)
        ((C*K*X*V+num 12*(E*Y))*((E*(Y*Y))*V)) := by
    dsimp only [DD,scaleDenominator]
    ipra_le 𝔞 E*𝔞 C*𝔞 K*𝔞 X*𝔞 Y*𝔞 V*𝔞 V*sl small
  have tay := GaussianNamedAffineRemainderRate.diagonal_at nameF nameF nameF
    (data j (shifted z B h D) (R+one) (B*D) a C E T) (data j z R B a C E T)
    (data (succ j) z R B a C E T) (ofGaussian h D)
    (GaussianEulerLogarithmicCompactTaylor.quadraticNumerator j R C E T X)
    (GaussianEulerLogarithmicCompactTaylor.quadraticDenominator E Y) (num 12) p
    (GaussianEulerLogarithmicCompactTaylor.diagonal_envelope j z R B a C E T h D X Y hs)
  have first := distance_radius_mono _ _ _ _ (C*K*X*V+num 12*(E*Y)) DD oldDen den firstNative tay
  have last := distance_radius_mono _ _ _ _ (C*L*X*V) DD ey den
    (le_of_eq_add (d := zero) (by dsimp only [DD,scaleDenominator]; ipra_ring))
    (linear_term_bound p j z R B a C E T h D X Y hs)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [gain,scaleDenominator,V,K,L]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den first last)

theorem diagonal_envelope (j z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx]
    GaussianNamedLipschitzRate.diagonalEnvelope nameF nameF
      (data j (shifted z B h D) (R+one) (B*D) a C E T) (data j z R B a C E T)
      (gain j R C E T X) (scaleDenominator E Y) (num 12) := by
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a)
      (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift h) (Syn.shift D) (Syn.shift X) (Syn.shift Y) :=
    by simpa only [Fm.shift,Syn.shift,GaussianEulerLogarithmicTaylorGrid.subst_source] using hs.shift
  refine .allI ?_
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalNumerator,
    GaussianNamedLipschitzRate.diagonalDenominator,GaussianEulerLogarithmicIntervalName.subst_data,
    GaussianEulerParameterExponentialIncrement.subst_shifted,subst_gain,subst_scaleDenominator,
    PTm.subst_add,PTm.subst_mul,PTm.subst_num,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,point,Syn.shift] using
    original_diagonal (var 0) (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a) (Syn.shift C)
      (Syn.shift E) (Syn.shift T) (Syn.shift h) (Syn.shift D) (Syn.shift X) (Syn.shift Y) ss

theorem original_observations (p q j z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (point p j (shifted z B h D) (R+one) (B*D) a C E T) (point q j z R B a C E T)
      (numerator p q j R C E T X Y) (denominator p q E Y) :=
  GaussianNamedLipschitzRate.independent_at nameF nameF
    (data j (shifted z B h D) (R+one) (B*D) a C E T) (data j z R B a C E T)
    (gain j R C E T X) (scaleDenominator E Y) (num 12) p q
    (positive_product _ _ hs.andE₁.andE₁.andE₂.andE₁ hs.andE₂.andE₂.andE₁)
    (name_regular _ _ _ _ _ _ _ _ (shifted_source z R B a C E T h D X Y hs))
    (name_regular _ _ _ _ _ _ _ _ hs.andE₁) (diagonal_envelope j z R B a C E T h D X Y hs)

theorem actual_original_compact_logarithmic_parameter_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    (source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ⟶
      distanceBounded (point (var 0) (var 2) (shifted (var 3) (var 5) (var 10) (var 11))
        (var 4+one) (var 5*var 11) (var 6) (var 7) (var 8) (var 9))
        (point (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
        (numerator (var 0) (var 1) (var 2) (var 4) (var 7) (var 8) (var 9) (var 12) (var 13))
        (denominator (var 0) (var 1) (var 8) (var 13))) :=
  closeUniv 14 (.impI (original_observations _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCompactParameterRate
