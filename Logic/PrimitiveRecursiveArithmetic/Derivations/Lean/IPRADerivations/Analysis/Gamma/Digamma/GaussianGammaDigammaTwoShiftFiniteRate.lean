import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaTwoShiftSecants
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaTwoShiftLogGap
import IPRADerivations.Analysis.Stirling.GaussianStirlingTailComparison

/-!
# Finite normalized two-shift log-Gamma rate

The two outside unit chords and the exact harmonic cutoff gaps bound
the normalized logarithmic difference with an explicit dyadic error.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftFiniteRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaHarmonicCells (point_fraction_represents)
open GaussianGammaDigammaTwoShiftSecants (logSample leftCost rightCost lower_secant upper_secant unit_chord_sample)
open GaussianHarmonicLogarithmName (sample)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qadd qmul qzero positive_product)
open GaussianRationalMetric (qsub qnegative bounded distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qadd_sub_cancel)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianStirlingTailComparison (point_add_upper_same)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle upper_of_order)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem log_gap_at (p a y b k : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hy : Γ ⊢[PRAAx] le one y)
    (hy2 : Γ ⊢[PRAAx] le a (two*y)) (hA : Γ ⊢[PRAAx] le a (y+k))
    (hY : Γ ⊢[PRAAx] le y (a+k)) :
    Γ ⊢[PRAAx] distanceBounded (sample p y b) (sample p a b) (two*k) a := by
  let goal := distanceBounded (sample p y b) (sample p a b) (two*k) a
  apply (le_total (Γ := Γ) y a).orE (χ := goal)
  · have h : (le y a :: Γ) ⊢[PRAAx] le y a := Prf.hyp0
    have gap := AnalyticNumberTheory.BlockFamily.monus_le_monus (Γ := le y a :: Γ) (c := y) hA.wk
    have gap' : (le y a :: Γ) ⊢[PRAAx] le (monus a y) k :=
      le_congr (.eqRefl _) ((congrMonus (add_comm y k) (.eqRefl y)).eqTrans (add_monus _ _)) gap
    have e := le_mul_mono hy2.wk gap'
    have raw := GaussianGammaDigammaTwoShiftLogGap.gap p a y b (two*k) a hy.wk h ha.wk
      (le_congr (.eqRefl _) (by ipra_ring) e)
    exact distance_symmetric _ _ _ _ ha.wk raw
  · have h : (le a y :: Γ) ⊢[PRAAx] le a y := Prf.hyp0
    have gap := AnalyticNumberTheory.BlockFamily.monus_le_monus (Γ := le a y :: Γ) (c := a) hY.wk
    have gap' : (le a y :: Γ) ⊢[PRAAx] le (monus y a) k :=
      le_congr (.eqRefl _) ((congrMonus (add_comm a k) (.eqRefl a)).eqTrans (add_monus _ _)) gap
    have twice : (le a y :: Γ) ⊢[PRAAx] le k (two*k) :=
      le_congr (.eqRefl _) (by ipra_ring) (le_add_right k k)
    exact GaussianGammaDigammaTwoShiftLogGap.gap p y a b (two*k) a ha.wk h ha.wk
      (le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono (le_refl a) (le_trans gap' twice)))

theorem weighted_distance (c x y M K D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hc : Γ ⊢[PRAAx] bounded c M one) (h : Γ ⊢[PRAAx] distanceBounded x y K D) :
    Γ ⊢[PRAAx] distanceBounded (qmul c x) (qmul c y) (M*K) D :=
  GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference c x y).eqSymm
    (.eqRefl _) (one_mul _) (GaussianRationalReciprocal.bounded_product c (qsub x y) M one K D (le_refl one) hD hc h)

theorem fraction_bound (r b M : PTm n) (hb : Γ ⊢[PRAAx] le one b) (h : Γ ⊢[PRAAx] le r (M*b)) :
    Γ ⊢[PRAAx] bounded (fraction r b) M one :=
  GaussianEulerExponentCompactBounds.fraction_bound r b M hb h

private theorem correction_distance (p a y b r k M : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hs : Γ ⊢[PRAAx] source y b) (hr : Γ ⊢[PRAAx] le r (M*b))
    (h : Γ ⊢[PRAAx] distanceBounded (sample p y b) (sample p a b) k a) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (qmul (fraction r b) (qsub (logSample p (y+b) b) (logSample p y b)))
        (qmul (fraction r b) (sample p a b))) qzero
      (M*k*unit p+num 5*M*a) (a*unit p) := by
  let f := fraction r b
  let U := unit p
  let x := qsub (logSample p (y+b) b) (logSample p y b)
  let l := sample p y b
  let z := sample p a b
  have hU := unit_positive (Γ := Γ) p
  have sum := GaussianReconstructionRoots.distance_triangle x l z (num 5) U k a hU ha (unit_chord_sample p y b hs) h
  have wide := weighted_distance f x z M _ _ (positive_product _ _ hU ha) (fraction_bound r b M hs.andE₂ hr) sum
  have e := GaussianRationalReconstruction.qsub_zero_right (Γ := Γ) (qsub (qmul f x) (qmul f z))
    (GaussianRationalMetric.qsub_canonical _ _)
  exact GaussianRationalReciprocal.bound_congr e.eqSymm (by ipra_ring) (by ipra_ring) wide

def raw (p a u b r : PTm n) : PTm n :=
  qsub (qsub (logSample p (u+b+r) b) (logSample p (u+b) b)) (qmul (fraction r b) (sample p a b))

private theorem common_translation (x y w A U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] upper (fstT x) (fstT y) A U) :
    Γ ⊢[PRAAx] upper (fstT (qsub x w)) (fstT (qsub y w)) A U :=
  upper_congr (.eqRefl _) (.eqRefl _) (add_zero _) (.eqRefl _)
    (point_add_upper_same x y (qnegative w) (qnegative w) A zero U hU h
      (upper_of_order _ _ _ _ (le_refl _)))

def leftError (u b r M : PTm n) : PTm n := leftCost u b r+num 5*M
def rightError (u b r M : PTm n) : PTm n := rightCost u b r+num 5*M

theorem raw_rate (p a u b r k M : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hs : Γ ⊢[PRAAx] source u b)
    (hr : Γ ⊢[PRAAx] le one r) (hR : Γ ⊢[PRAAx] le r (M*b))
    (hL : Γ ⊢[PRAAx] distanceBounded (sample p u b) (sample p a b) k a)
    (hH : Γ ⊢[PRAAx] distanceBounded (sample p (u+b+r) b) (sample p a b) k a) :
    Γ ⊢[PRAAx]
      (upper (fstT qzero) (fstT (raw p a u b r)) (M*k*unit p+leftError u b r M*a) (a*unit p) ⋏
       upper (fstT (raw p a u b r)) (fstT qzero) (M*k*unit p+rightError u b r M*a) (a*unit p)) := by
  let U := unit p
  let c := u+b+r
  let d := u+b
  let f := fraction r b
  let w := qmul f (sample p a b)
  let Z := qzero (n := n)
  let L := qsub (qmul f (qsub (logSample p d b) (logSample p u b))) w
  let R := qsub (qmul f (qsub (logSample p (c+b) b) (logSample p c b))) w
  let E := M*k*U+num 5*M*a
  have hp := unit_positive (Γ := Γ) p
  have hD := positive_product _ _ ha hp
  have hc : Γ ⊢[PRAAx] source c b :=
    .andI (le_trans (le_trans hs.andE₁ (le_add_right _ _)) (le_add_right _ _)) hs.andE₂
  have left := correction_distance p a u b r k M ha hs hR hL
  have right := correction_distance p a c b r k M ha hc hR hH
  have before := scalar_upper Z L E (a*U) hD (distance_symmetric _ _ _ _ hD left)
  have after := scalar_upper R Z E (a*U) hD right
  have lower := common_translation _ _ w _ U hp (lower_secant p u b r hs hr)
  have upper' := common_translation _ _ w _ U hp (upper_secant p u b r hs hr)
  refine .andI ?_ ?_
  · apply upper_mono _ _ _ _ _ _ (positive_product _ _ hD hp)
      (upper_triangle _ _ _ _ _ _ _ before lower)
    exact le_of_eq_add (d := zero) (by unfold leftError E U; ipra_ring)
  · apply upper_mono _ _ _ _ _ _ (positive_product _ _ hp hD)
      (upper_triangle _ _ _ _ _ _ _ upper' after)
    exact le_of_eq_add (d := zero) (by unfold rightError E U; ipra_ring)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftFiniteRate
