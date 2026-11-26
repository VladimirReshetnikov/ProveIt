import IPRADerivations.Analysis.Barnes.Deflation.GaussianBarnesCanonicalDeflatedNamed
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaPolynomialPrimitive

/-!
# The internal translated power of a regular Barnes argument

The actual rational power is evaluated at a retimed observation of the
original name. The certified half-unit disk gives the unit power bound
and controls comparison to the same power at a shared late input clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedTranslatedPower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalDeflatedNamed (neighborhood neighborhood_at)
open GaussianBarnesCanonicalDeflatedFactor (translatedValue translatedPower)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaEulerHeadLower (translated)
open GaussianFastValueCut (exponent query_budget recode_distance_bound)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianNameEquivalence (point_at)
open GaussianNameArithmetic (sum_distance)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalPowerDifference (distance_refl_zero unit_disk_power_difference bounded_power_integer)
open GaussianRationalReciprocal (bound_congr power_canonical)
open GaussianExponentialReference (unit_monotone recode_fixed)
open ComplexLogarithmRemainder (normSq normSq_scale)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def frozen (f : PR 2) (k x m : PTm n) : PTm n :=
  translatedPower (rawGaussian (ap2 f k x)) (rawDen (ap2 f k x)) m

def rawF (f : PR 2) : PR 2 := PTm.toPR
  (frozen f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)

def nameF (f : PR 2) : PR 2 := GaussianFastValueCut.nameF (rawF f)
def data (x m : PTm n) : PTm n := GaussianFastValueCut.nameData m (pairT x m)

@[simp] theorem subst_frozen {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (k x m : PTm n) :
    Syn.subst σ (frozen f k x m) = frozen f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ m) := by simp [frozen]

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (x m : PTm n) :
    Syn.subst σ (data x m) = data (Syn.subst σ x) (Syn.subst σ m) := by simp [data]

theorem raw_at (f : PR 2) (p x m : PTm n) : Γ ⊢[PRAAx] ap2 (rawF f) p (pairT x m) ≐ frozen f p x m := by
  let X := pairT x m
  have read : Γ ⊢[PRAAx] ap2 (rawF f) p X ≐ frozen f p (fstT X) (sndT X) := by
    simpa [rawF,ap2] using toPR_eq (Γ := Γ) (frozen f (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,X]
  exact read.eqTrans (by
    ipra_congr (frozen f (var 0) (var 1) (var 2) : PTm 3) with
      [.eqRefl p, fst_pair x m, snd_pair x m] using [X])

theorem sample_at (f : PR 2) (p x m : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF f) p (data x m) ≐ frozen f (exponent m p) x m := by
  have a := GaussianFastValueCut.name_at (Γ := Γ) (rawF f) m (pairT x m) p
  exact a.eqTrans ((GaussianNameArithmetic.recode_congr (raw_at f (exponent m p) x m)).eqTrans
    (recode_fixed _ (power_canonical _ _)))

theorem translated_disk (z B m : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] GaussianBarnesCanonicalDeflatedHead.neighborhood z B m) :
    Γ ⊢[PRAAx] bounded (translatedValue z B m) one one := by
  let d := translated z B m
  have native : Γ ⊢[PRAAx] le (two*two*normSq d) (B*B) :=
    le_congr (normSq_scale two d) (.eqRefl _) h
  have scale : Γ ⊢[PRAAx] le (normSq d) (two*two*normSq d) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (normSq d)
      (positive_product _ _ (le_succ_self one) (le_succ_self one)))
  have guard : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded d (one*B) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_trans scale native)
  exact GaussianGammaEulerHead.fraction_disk d one B hB guard

theorem frozen_bound (f : PR 2) (p x m : PTm n) (h : Γ ⊢[PRAAx] neighborhood f x m) :
    Γ ⊢[PRAAx] bounded (frozen f p x m) one one := by
  let Q := ap2 f p x
  have b := translated_disk (rawGaussian Q) (rawDen Q) m (raw_den_positive Q) (neighborhood_at f p x m h)
  exact bound_congr (.eqRefl _) (GaussianPolynomialPerturbation.one_power m) (.eqRefl _)
    (bounded_power_integer (translatedValue (rawGaussian Q) (rawDen Q) m) one m b)

private theorem frozen_distance (f : PR 2) (p q x m : PTm n)
    (h : Γ ⊢[PRAAx] pointCN f x) (hn : Γ ⊢[PRAAx] neighborhood f x m) :
    Γ ⊢[PRAAx] distanceBounded (frozen f p x m) (frozen f q x m) (m*(unit p+unit q)) (unit p*unit q) := by
  let a := ap2 f p x
  let b := ap2 f q x
  let K := unit p*unit q
  let A := unit p+unit q
  let c := naturalPoint m
  let u := translatedValue (rawGaussian a) (rawDen a) m
  let v := translatedValue (rawGaussian b) (rawDen b) m
  have hK := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  have ha := raw_den_positive (Γ := Γ) a
  have hb := raw_den_positive (Γ := Γ) b
  have near := recode_distance_bound a b A K hK (point_at f x p q h)
  have fixed := sum_distance _ _ c c A zero K hK near (distance_refl_zero c K hK)
  have e : Γ ⊢[PRAAx] u ≐ GaussianRationalHorner.qadd (GaussianFastValueCut.recode a) c :=
    GaussianEulerBetaPolynomialPrimitive.linear_as_sum _ _ _ ha
  have e' : Γ ⊢[PRAAx] v ≐ GaussianRationalHorner.qadd (GaussianFastValueCut.recode b) c :=
    GaussianEulerBetaPolynomialPrimitive.linear_as_sum _ _ _ hb
  exact unit_disk_power_difference u v A K m hK (translated_disk _ _ _ ha (neighborhood_at f p x m hn))
    (translated_disk _ _ _ hb (neighborhood_at f q x m hn))
    (distance_congr e.eqSymm e'.eqSymm (add_zero _) (.eqRefl _) fixed)

theorem regular (f : PR 2) (x m : PTm n) (h : Γ ⊢[PRAAx] pointCN f x)
    (hn : Γ ⊢[PRAAx] neighborhood f x m) : Γ ⊢[PRAAx] pointCN (nameF f) (data x m) := by
  apply GaussianFastValueCut.name_fast
  refine .allI (.allI ?_)
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have H : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  have N : Δ ⊢[PRAAx] neighborhood f (sh x) (sh m) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hn.shift.shift
  simpa only [GaussianFastValueCut.regular,subst_pairT,Syn.shift,sh,Δ] using
    distance_congr (raw_at f (var 1) (sh x) (sh m)).eqSymm (raw_at f (var 0) (sh x) (sh m)).eqSymm
      (.eqRefl _) (.eqRefl _) (frozen_distance f (var 1) (var 0) (sh x) (sh m) H N)

theorem name_bound (f : PR 2) (x m : PTm n) (hn : Γ ⊢[PRAAx] neighborhood f x m) :
    Γ ⊢[PRAAx] sampleBound (nameF f) (data x m) one := by
  refine .allI ?_
  let sh (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  have N : Δ ⊢[PRAAx] neighborhood f (sh x) (sh m) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hn.shift
  simpa only [sampleBound,subst_data,Syn.shift,sh,Δ,one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using
    bound_congr (sample_at f (var 0) (sh x) (sh m)).eqSymm (.eqRefl _) (.eqRefl _)
      (frozen_bound f (exponent (sh m) (var 0)) (sh x) (sh m) N)

theorem late_observation (f : PR 2) (p k x m : PTm n)
    (h : Γ ⊢[PRAAx] pointCN f x) (hn : Γ ⊢[PRAAx] neighborhood f x m)
    (hk : Γ ⊢[PRAAx] le (exponent m p) k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x m)) (frozen f k x m) two (unit p) := by
  let t := exponent m p
  have e : Γ ⊢[PRAAx] le (m*unit p) (unit t) := query_budget m p
  have b : Γ ⊢[PRAAx] le (m*unit p) (unit k) := le_trans e (unit_monotone hk)
  have split := add_le_add₂ (mul_le_mul_right (unit k) e) (mul_le_mul_right (unit t) b)
  have pay : Γ ⊢[PRAAx] le ((m*(unit t+unit k))*unit p) (two*(unit t*unit k)) :=
    le_congr (by ipra_ring) (by ipra_ring) split
  exact distance_congr (sample_at f p x m).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive k)) (unit_positive p) pay
      (frozen_distance f t k x m h hn))

theorem actual_Barnes_named_translated_power_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((pointCN f (var 0) ⋏ neighborhood f (var 0) (var 1)) ⟶ pointCN (nameF f) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (regular f _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedTranslatedPower
