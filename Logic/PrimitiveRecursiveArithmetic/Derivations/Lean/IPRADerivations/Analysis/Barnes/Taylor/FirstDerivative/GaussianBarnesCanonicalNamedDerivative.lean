import IPRADerivations.Analysis.Geometry.GaussianNamedDiskDemandReadback
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalValueDerivativeProperness
import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamed

/-!
# Lift the original Barnes derivative to regular Gaussian names

The supplied primitive-recursive modulus sets a finite observation
clock. The resulting program runs the original rational derivative
at that Gaussian sample and is regular on each certified input disk.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalNamedDemand (source data native_source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical positive_product)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "V" => GaussianBarnesCanonicalValueDerivative.nameF
local notation "VD" => GaussianBarnesCanonicalValueDerivative.data
local notation "disk" => GaussianBarnesCanonicalLogCofinal.source

structure Modulus where
  inputClockF : PR 2
  uniform_input : ∀ {m : ℕ} {Δ : List (Fm PTm m)} (z w R B D p : PTm m),
    (Δ ⊢[PRAAx] disk z R B) → (Δ ⊢[PRAAx] disk w R D) →
    (Δ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) one (unit (ap2 inputClockF R p))) →
    (Δ ⊢[PRAAx] independentRate V V (VD z R B) (VD w R D) one (unit p))

@[simp] theorem subst_rationalData {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (VD z R B) = VD (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [GaussianBarnesCanonicalValueDerivative.data,GaussianBarnesCanonicalValueDerivativeJoin.derivativeData,
    GaussianNamedNativeProductDerivativeRate.derivativeData]

private def rationalTerm : PTm 3 := VD (var 0) (var 1) (var 2)

private theorem rational_term_at (z R B : PTm n) : inst3 rationalTerm z R B = VD z R B :=
  by simp [rationalTerm,inst3]

def rationalMap (modulus : Modulus) : GaussianNamedDiskDemandLift.RationalMap where
  evaluator := V
  rationalData := rationalTerm
  inputClockF := modulus.inputClockF
  uniform_input z w R B D p hz hw h := by
    simpa only [rational_term_at] using modulus.uniform_input z w R B D p hz hw h

private theorem map_evaluator (modulus : Modulus) : (rationalMap modulus).evaluator = V := rfl

abbrev nameF (modulus : Modulus) (f : PR 2) : PR 2 := GaussianNamedDiskDemandLift.nameF (rationalMap modulus) f
abbrev clock (modulus : Modulus) (p R : PTm n) : PTm n := GaussianNamedDiskDemandLift.clock (rationalMap modulus) p R

def frozenData (f : PR 2) (k x R : PTm n) : PTm n :=
  VD (rawGaussian (ap2 f k x)) R (rawDen (ap2 f k x))

@[simp] theorem subst_frozenData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x R : PTm n) :
    Syn.subst σ (frozenData f k x R) = frozenData f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ R) := by
  simp [frozenData]

private theorem map_frozen (modulus : Modulus) (f : PR 2) (k x R : PTm n) :
    GaussianNamedDiskDemandLift.frozenData (rationalMap modulus) f k x R = frozenData f k x R :=
  rational_term_at _ _ _

theorem sample_at (modulus : Modulus) (f : PR 2) (p x R : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF modulus f) p (data x R) ≐ ap2 V (succ p) (frozenData f (clock modulus p R) x R) := by
  simpa only [GaussianNamedDiskDemandLift.sample,map_frozen,map_evaluator] using
    GaussianNamedDiskDemandLift.sample_at (rationalMap modulus) f p x R

theorem clock_demand (modulus : Modulus) (p R s : PTm n) (hs : Γ ⊢[PRAAx] le s (succ p)) :
    Γ ⊢[PRAAx] le (succ (ap2 modulus.inputClockF R s)) (clock modulus p R) :=
  GaussianNamedDiskDemandLift.clock_demand (rationalMap modulus) p R s hs

theorem late_rate (modulus : Modulus) (f g : PR 2) (s k l x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R) (he : Γ ⊢[PRAAx] crossEquivalent f g x y)
    (hk : Γ ⊢[PRAAx] le (succ (ap2 modulus.inputClockF R s)) k)
    (hl : Γ ⊢[PRAAx] le (succ (ap2 modulus.inputClockF R s)) l) :
    Γ ⊢[PRAAx] independentRate V V (frozenData f k x R) (frozenData g l y R) one (unit s) := by
  simpa only [map_frozen,map_evaluator] using GaussianNamedDiskDemandLift.late_rate (rationalMap modulus) f g s k l x y R hf hg he hk hl

theorem proper (modulus : Modulus) (f g : PR 2) (x y R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hg : Γ ⊢[PRAAx] source g y R) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF modulus f) (nameF modulus g) (data x R) (data y R) :=
  GaussianNamedDiskDemandLift.proper (rationalMap modulus) f g x y R hf hg h

theorem name_regular (modulus : Modulus) (f : PR 2) (x R : PTm n) (h : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] pointCN (nameF modulus f) (data x R) :=
  GaussianNamedDiskDemandLift.name_regular (rationalMap modulus) f x R h

theorem frozen_observations (modulus : Modulus) (f : PR 2) (p q s k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock modulus s R) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF modulus f) p (data x R)) (ap2 V q (frozenData f k x R))
      (rateNumerator one (unit s) p q) (rateDenominator (unit s) p q) := by
  simpa only [map_frozen,map_evaluator] using
    GaussianNamedDiskDemandReadback.frozen_observations (rationalMap modulus) f p q s k x R hf hk

theorem frozen_rate (modulus : Modulus) (f : PR 2) (s k x R : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hk : Γ ⊢[PRAAx] le (clock modulus s R) k) :
    Γ ⊢[PRAAx] independentRate (nameF modulus f) V (data x R) (frozenData f k x R) one (unit s) := by
  simpa only [map_frozen,map_evaluator] using
    GaussianNamedDiskDemandReadback.frozen_rate (rationalMap modulus) f s k x R hf hk

private theorem constant_observations (modulus : Modulus) (p q z R B : PTm n) (h : Γ ⊢[PRAAx] disk z R B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF modulus constantF) p (data (ofGaussian z B) R)) (ap2 V q (VD z R B))
      (unit p+unit q) (unit p*unit q) := by
  let x := ofGaussian z B
  let k := clock modulus p R
  let y := ap2 constantF k x
  have admitted := native_source constantF k x R (GaussianBarnesCanonicalNamed.constant_source z R B h)
  have same : Γ ⊢[PRAAx] ofGaussian (rawGaussian y) (rawDen y) ≐ x :=
    (GaussianNameArithmetic.recode_congr (constant_at k x)).eqTrans
      (GaussianExponentialReference.recode_fixed x (ofGaussian_canonical z B h.andE₁))
  have he := GaussianBarnesCanonicalValueDerivativeProperness.proper (rawGaussian y) z R (rawDen y) B admitted h same
  have qNear := cross_at V V (frozenData constantF k x R) (VD z R B) (succ p) q he
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_succ_self p)
  have widened := distance_radius_mono _ _ _ _ (unit p+unit q) (unit p*unit q)
    (positive_product _ _ (unit_positive (succ p)) (unit_positive q))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (by ipra_le 𝔞(unit q*unit q)*sl grow) qNear
  exact distance_congr (sample_at modulus constantF p x R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) widened

theorem constant_cross (modulus : Modulus) (z R B : PTm n) (h : Γ ⊢[PRAAx] disk z R B) :
    Γ ⊢[PRAAx] crossEquivalent (nameF modulus constantF) V (data (ofGaussian z B) R) (VD z R B) := by
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] disk (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,Syn.shift,sh,Δ,GaussianBarnesCanonicalNamedDemand.subst_data,
    subst_rationalData,GaussianRationalHorner.subst_ofGaussian] using
    constant_observations modulus (var 1) (var 0) (sh z) (sh R) (sh B) hs

theorem bind (modulus : Modulus) (f : PR 2) (x z R B : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hz : Γ ⊢[PRAAx] disk z R B)
    (he : Γ ⊢[PRAAx] crossEquivalent f constantF x (ofGaussian z B)) :
    Γ ⊢[PRAAx] crossEquivalent (nameF modulus f) V (data x R) (VD z R B) :=
  cross_trans (nameF modulus f) (nameF modulus constantF) V (data x R) (data (ofGaussian z B) R) (VD z R B)
    (proper modulus f constantF x (ofGaussian z B) R hf (GaussianBarnesCanonicalNamed.constant_source z R B hz) he)
    (constant_cross modulus z R B hz)

theorem actual_Barnes_named_derivative_regular_closed (modulus : Modulus) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (source f (var 0) (var 1) ⟶ pointCN (nameF modulus f) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular modulus f _ _ Prf.hyp0))

theorem actual_Barnes_named_derivative_late_rational_rate_closed (modulus : Modulus) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 0) (var 1) ⟶ le (clock modulus (var 2) (var 1)) (var 3) ⟶
        independentRate (nameF modulus f) V (data (var 0) (var 1)) (frozenData f (var 3) (var 0) (var 1))
          one (unit (var 2))) :=
  closeUniv 4 (.impI (.impI (frozen_rate modulus f _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_Barnes_named_derivative_rational_binding_closed (modulus : Modulus) (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 0) (var 2) ⟶ disk (var 1) (var 2) (var 3) ⟶
        crossEquivalent f constantF (var 0) (ofGaussian (var 1) (var 3)) ⟶
        crossEquivalent (nameF modulus f) V (data (var 0) (var 2)) (VD (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (bind modulus f _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedDerivative
