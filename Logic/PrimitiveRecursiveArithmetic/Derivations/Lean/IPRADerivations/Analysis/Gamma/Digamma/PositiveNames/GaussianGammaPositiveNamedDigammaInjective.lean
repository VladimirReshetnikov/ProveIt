import IPRADerivations.Analysis.Gamma.Digamma.Comparison.Slopes.GaussianGammaDigammaCompactInverseSlope
import IPRADerivations.Analysis.Gamma.Digamma.PositiveNames.GaussianGammaPositiveNamedDigammaFrozen

/-!
# Injectivity of the original digamma on all positive real names

The two input names may use different positive margins and independent
rational encodings. At a common late clock the native lower slope bounds
the separation of their observations by the named digamma error.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedDigammaInjective

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaMinimumFreezeRational (numerator denominator frozen_rational_domain fraction_at)
open GaussianGammaPositiveNamedRationalFreeze (clock threshold_le)
open GaussianNameEquivalence (crossEquivalent cross_at point_at)
open GaussianNamedInverseRate (diagonal_rate)
open GaussianNamedPositiveDigamma (source nameF data)
open GaussianNamedRightHalfPlane (threshold radius)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "N" => GaussianGammaDigammaNative.nameF
local notation "fd" => GaussianGammaPositiveNamedDigammaFrozen.frozenData
local notation "gain" => GaussianGammaPositiveNamedDigammaFrozen.gain
local notation "scale" => GaussianGammaDigammaCompactInverseSlope.gain

def cap (f g : PR 2) (x y : PTm n) : PTm n := radius f x+radius g y

def outputCost (f g : PR 2) (x y A B : PTm n) : PTm n := ((gain f x A+two)+two)+(gain g y B+two)

def cost (f g : PR 2) (x y A B : PTm n) : PTm n := (two+scale (cap f g x y) (outputCost f g x y A B))+two

theorem frozen_observation (f : PR 2) (p k x A : PTm n) (hf : Γ ⊢[PRAAx] source f x A)
    (hk : Γ ⊢[PRAAx] le (clock f p one x A) k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data f x A)) (ap2 N p (fd f k x)) (gain f x A+two) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by unfold two; ipra_ring))
    (diagonal_rate _ _ _ _ _ _ p hp (GaussianGammaPositiveNamedDigammaFrozen.original_rate f p k x A hf hk))

private theorem frozen_input (f : PR 2) (p k x A : PTm n) (hf : Γ ⊢[PRAAx] source f x A)
    (hp : Γ ⊢[PRAAx] le p k) (ht : Γ ⊢[PRAAx] le (threshold A) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (fraction (numerator f k x) (denominator f k x)) two (unit p) := by
  have hu := unit_positive (Γ := Γ) p
  have hv := unit_positive (Γ := Γ) k
  have grow := GaussianExponentialReference.unit_monotone hp
  exact distance_congr (.eqRefl _) (fraction_at f k x A hf ht) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hu hv) hu
      (by unfold two; ipra_le 𝔞(unit p)*sl grow) (point_at f x p k hf.andE₁.andE₁))

theorem input_distance (f g : PR 2) (p x y A B : PTm n) (hf : Γ ⊢[PRAAx] source f x A)
    (hg : Γ ⊢[PRAAx] source g y B)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data f x A) (data g y B)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g p y) (cost f g x y A B) (unit p) := by
  let l := clock f p one x A
  let r := clock g p one y B
  let k := p+(l+r)
  let M := cap f g x y
  have hl : Γ ⊢[PRAAx] le l k := le_trans (le_add_right _ _) (le_add_left _ _)
  have hr : Γ ⊢[PRAAx] le r k := le_trans (le_add_left _ _) (le_add_left _ _)
  have ml := le_trans (threshold_le (Γ := Γ) f p one x A) hl
  have mr := le_trans (threshold_le (Γ := Γ) g p one y B) hr
  have hP := unit_positive (Γ := Γ) p
  have hM : Γ ⊢[PRAAx] le one M := le_trans (GaussianNameBounds.U_positive f x) (le_add_right _ _)
  have left := distance_symmetric _ _ _ _ hP (frozen_observation f p k x A hf hl)
  have right := frozen_observation g p k y B hg hr
  have middle := GaussianNameEquivalence.cross_diagonal_at p he
  have close := distance_triangle_same _ _ _ _ _ _ hP (distance_triangle_same _ _ _ _ _ _ hP left middle) right
  have d1 := frozen_rational_domain f k x A hf ml
  have d2 := frozen_rational_domain g k y B hg mr
  have m1 := le_trans d1.andE₂.andE₂ (mul_le_mul_right (denominator f k x) (le_add_right (radius f x) (radius g y)))
  have m2 := le_trans d2.andE₂.andE₂ (mul_le_mul_right (denominator g k y) (le_add_left (radius g y) (radius f x)))
  have finite := GaussianGammaDigammaCompactInverseSlope.input_distance _ _ _ _ M p (outputCost f g x y A B)
    d1.andE₁ d2.andE₁ hM m1 m2 close
  exact distance_triangle_same _ _ _ _ _ _ hP
    (distance_triangle_same _ _ _ _ _ _ hP (frozen_input f p k x A hf (le_add_right _ _) ml) finite)
    (distance_symmetric _ _ _ _ hP (frozen_input g p k y B hg (le_add_right _ _) mr))

theorem injective (f g : PR 2) (x y A B : PTm n) (hf : Γ ⊢[PRAAx] source f x A)
    (hg : Γ ⊢[PRAAx] source g y B)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data f x A) (data g y B)) :
    Γ ⊢[PRAAx] crossEquivalent f g x y := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (cost f g x y A B) hf.andE₁.andE₁ hg.andE₁.andE₁ (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have h1 : Δ ⊢[PRAAx] source f (sh x) (sh A) := by simpa [Δ,Fm.shift,sh,Syn.shift] using hf.shift
  have h2 : Δ ⊢[PRAAx] source g (sh y) (sh B) := by simpa [Δ,Fm.shift,sh,Syn.shift] using hg.shift
  have h3 : Δ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data f (sh x) (sh A)) (data g (sh y) (sh B)) :=
    by simpa [Δ,Fm.shift,sh,Syn.shift] using he.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,sh,cost,outputCost,cap,
    GaussianGammaDigammaCompactInverseSlope.gain,GaussianGammaPositiveNamedDigammaFrozen.subst_gain,
    GaussianNamedRightHalfPlane.subst_radius,PTm.subst_mul,PTm.subst_add,PTm.subst_num,two,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    input_distance f g (var 0) (sh x) (sh y) (sh A) (sh B) h1 h2 h3

theorem actual_original_positive_named_digamma_injective_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((source f (var 0) (var 2) ⋏ source g (var 1) (var 3)) ⟶
        crossEquivalent (nameF f) (nameF g) (data f (var 0) (var 2)) (data g (var 1) (var 3)) ⟶
        crossEquivalent f g (var 0) (var 1)) :=
  closeUniv 4 (.impI (.impI (injective f g _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedDigammaInjective
