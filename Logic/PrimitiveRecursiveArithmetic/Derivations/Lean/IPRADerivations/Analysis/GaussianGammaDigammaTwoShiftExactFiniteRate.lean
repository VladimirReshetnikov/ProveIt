import IPRADerivations.Analysis.GaussianGammaDigammaTwoShiftFiniteRate

/-!
# Exact rational width in the original two-shift Gamma secants

Keep the actual factor r/b in the two endpoint corrections. This
retains r·k/(a·b) in the leading finite error, with no integer
enlargement of the interval width.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftExactFiniteRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radius_bounded)
open GaussianGammaDigammaTwoShiftFiniteRate (raw)
open GaussianGammaDigammaTwoShiftSecants (logSample leftCost rightCost lower_secant upper_secant unit_chord_sample)
open GaussianHarmonicLogarithmName (sample)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qmul qzero positive_product)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingGammaFractionalIncrementObservations (scalar_upper)
open GaussianStirlingTailComparison (point_add_upper_same)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle upper_of_order)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def leftSlack (u b r : PTm n) : PTm n := b*leftCost u b r+num 5*r
def rightSlack (u b r : PTm n) : PTm n := b*rightCost u b r+num 5*r

@[simp] theorem subst_leftSlack {m : ℕ} (σ : Fin n → PTm m) (u b r : PTm n) :
    Syn.subst σ (leftSlack u b r) = leftSlack (Syn.subst σ u) (Syn.subst σ b) (Syn.subst σ r) := by
  simp [leftSlack,leftCost,GaussianStirlingGammaFractionalIncrementObservations.weightedCost,
    GaussianStirlingGammaFractionalIncrementObservations.scaleCost,GaussianNameRingLaws.three]

@[simp] theorem subst_rightSlack {m : ℕ} (σ : Fin n → PTm m) (u b r : PTm n) :
    Syn.subst σ (rightSlack u b r) = rightSlack (Syn.subst σ u) (Syn.subst σ b) (Syn.subst σ r) := by
  simp [rightSlack,rightCost,GaussianStirlingGammaFractionalIncrementObservations.weightedCost,
    GaussianStirlingGammaFractionalIncrementObservations.scaleCost,GaussianNameRingLaws.three]

theorem correction_distance (p a y b r k : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hs : Γ ⊢[PRAAx] source y b)
    (h : Γ ⊢[PRAAx] distanceBounded (sample p y b) (sample p a b) k a) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (qmul (fraction r b) (qsub (logSample p (y+b) b) (logSample p y b)))
        (qmul (fraction r b) (sample p a b))) qzero
      (r*k*unit p+num 5*r*a) ((a*b)*unit p) := by
  let f := fraction r b
  let U := unit p
  let x := qsub (logSample p (y+b) b) (logSample p y b)
  let l := sample p y b
  let z := sample p a b
  have hU := unit_positive (Γ := Γ) p
  have hb := hs.andE₂
  have sum := GaussianReconstructionRoots.distance_triangle x l z (num 5) U k a hU ha (unit_chord_sample p y b hs) h
  have hf := bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point r b hb).eqSymm
    (.eqRefl _) (.eqRefl _) (radius_bounded r b hb)
  have near := bound_congr (GaussianRationalRoundedPower.multiplication_difference f x z).eqSymm
    (.eqRefl _) (.eqRefl _) (bounded_product f (qsub x z) r b _ _ hb (positive_product _ _ hU ha) hf sum)
  have e := GaussianRationalReconstruction.qsub_zero_right (Γ := Γ) (qsub (qmul f x) (qmul f z))
    (GaussianRationalMetric.qsub_canonical _ _)
  exact bound_congr e.eqSymm (by ipra_ring) (by ipra_ring) near

private theorem common_translation (x y w A U : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] upper (fstT x) (fstT y) A U) :
    Γ ⊢[PRAAx] upper (fstT (qsub x w)) (fstT (qsub y w)) A U :=
  upper_congr (.eqRefl _) (.eqRefl _) (add_zero _) (.eqRefl _)
    (point_add_upper_same x y (qnegative w) (qnegative w) A zero U hU h
      (upper_of_order _ _ _ _ (le_refl _)))

theorem raw_rate (p a u b r k : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hs : Γ ⊢[PRAAx] source u b)
    (hr : Γ ⊢[PRAAx] le one r)
    (hL : Γ ⊢[PRAAx] distanceBounded (sample p u b) (sample p a b) k a)
    (hH : Γ ⊢[PRAAx] distanceBounded (sample p (u+b+r) b) (sample p a b) k a) :
    Γ ⊢[PRAAx]
      (upper (fstT qzero) (fstT (raw p a u b r)) (r*k*unit p+leftSlack u b r*a) ((a*b)*unit p) ⋏
       upper (fstT (raw p a u b r)) (fstT qzero) (r*k*unit p+rightSlack u b r*a) ((a*b)*unit p)) := by
  let U := unit p
  let c := u+b+r
  let d := u+b
  let f := fraction r b
  let w := qmul f (sample p a b)
  let Z := qzero (n := n)
  let L := qsub (qmul f (qsub (logSample p d b) (logSample p u b))) w
  let R := qsub (qmul f (qsub (logSample p (c+b) b) (logSample p c b))) w
  let E := r*k*U+num 5*r*a
  let D := (a*b)*U
  have hp := unit_positive (Γ := Γ) p
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ ha hs.andE₂) hp
  have hc : Γ ⊢[PRAAx] source c b :=
    .andI (le_trans (le_trans hs.andE₁ (le_add_right _ _)) (le_add_right _ _)) hs.andE₂
  have left := correction_distance p a u b r k ha hs hL
  have right := correction_distance p a c b r k ha hc hH
  have before := scalar_upper Z L E D hD (distance_symmetric _ _ _ _ hD left)
  have after := scalar_upper R Z E D hD right
  have lower := common_translation _ _ w _ U hp (lower_secant p u b r hs hr)
  have upper' := common_translation _ _ w _ U hp (upper_secant p u b r hs hr)
  refine .andI ?_ ?_
  · apply upper_mono _ _ _ _ _ _ (positive_product _ _ hD hp)
      (upper_triangle _ _ _ _ _ _ _ before lower)
    exact le_of_eq_add (d := zero) (by dsimp only [leftSlack,E,U,D]; ipra_ring)
  · apply upper_mono _ _ _ _ _ _ (positive_product _ _ hp hD)
      (upper_triangle _ _ _ _ _ _ _ upper' after)
    exact le_of_eq_add (d := zero) (by dsimp only [rightSlack,E,U,D]; ipra_ring)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftExactFiniteRate
