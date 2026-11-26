import IPRADerivations.Analysis.Exponential.GaussianExponentialRealPart
import IPRADerivations.Analysis.RationalArithmetic.Norms.GaussianSquaredNormUpper
import IPRADerivations.Analysis.Gamma.GaussianGammaRealValues

/-!
# Actual norm-radius transfer from equality of squared-norm names

Equal squared-norm names and regularity transfer an actual bound at query
p from G to F with only 2*2^-p. Late squared comparisons are evaluated at
2t+1; the existing finite squared-upper lemma extracts an ordinary radius.
One rational integer gap removes only the remaining auxiliary errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerVerticalNormTransfer

open_ipra
open GaussianExponentialRealPart (squareF squareData squarePrecision)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded qnormSq squaredTolerance qsub)
open GaussianRationalDistanceOrder (distance_radius_mono distance_congr distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem later_observations (F : PR 2) (x k p t : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x)
    (hk : Γ ⊢[PRAAx] le t k) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F k x) (ap2 F p x) (unit t+unit p) (unit t*unit p) := by
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) hk
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive k) (unit_positive p)) (positive_product _ _ (unit_positive t) (unit_positive p))
    (by ipra_le (𝔞(unit p)*𝔞(unit p))*sl grow) (GaussianNameEquivalence.point_at F x k p hf)

theorem square_clock_later (F : PR 2) (p x : PTm n) : Γ ⊢[PRAAx] le p (squarePrecision F p x) := by
  unfold squarePrecision GaussianFastValueCut.exponent
  exact le_add_right _ _

theorem cofinal_bound (F G : PR 2) (x y p S T t : PTm n)
    (hT : Γ ⊢[PRAAx] le one T) (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (he : Γ ⊢[PRAAx] crossEquivalent (squareF F) (squareF G) (squareData F x) (squareData G y))
    (hb : Γ ⊢[PRAAx] bounded (ap2 G p y) S T) : Γ ⊢[PRAAx]
    bounded (ap2 F p x) ((S*unit p+two*T)*unit t+num 4*(T*unit p)) ((T*unit p)*unit t) := by
  let H := t+t+one
  let k := squarePrecision F H x
  let j := squarePrecision G H y
  let P := unit p
  let U := unit t
  let Z := T*P*U
  let A := (S*P+T)*U+T*P
  have hP : Γ ⊢[PRAAx] le one P := unit_positive p
  have hU : Γ ⊢[PRAAx] le one U := unit_positive t
  have hZ : Γ ⊢[PRAAx] le one Z := positive_product _ _ (positive_product _ _ hT hP) hU
  have htH : Γ ⊢[PRAAx] le t H := le_of_eq_add (d := t+one) (by dsimp only [H]; ipra_ring)
  have hk : Γ ⊢[PRAAx] le t k := le_trans htH (square_clock_later F H x)
  have hj : Γ ⊢[PRAAx] le t j := le_trans htH (square_clock_later G H y)
  have realBound : Γ ⊢[PRAAx] bounded (ap2 G j y) A Z :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (by dsimp only [A,P,U]; ipra_ring) (by dsimp only [Z,P,U]; ipra_ring)
      (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (positive_product _ _ hU hP) hT
        (later_observations G y j p t hg hj) hb)
  have squareRaw := GaussianNameEquivalence.cross_at _ _ _ _ H H he
  have squareDistance := distance_congr (GaussianExponentialRealPart.square_sample F H x)
    (GaussianExponentialRealPart.square_sample G H y) (.eqRefl _) (.eqRefl _) squareRaw
  have squareScalar := GaussianGammaRealValues.scalar_radius_of_embedded_distance _ _ _ _
    (positive_product _ _ (unit_positive H) (unit_positive H)) squareDistance
  have bit : Γ ⊢[PRAAx] unit H ≐ two*unit (t+t) :=
    ((congrAp2 powF (by dsimp only [H]; ipra_ring : Γ ⊢[PRAAx] H ≐ succ (t+t)) (.eqRefl two)).eqTrans
      (pw_succ two (t+t))).eqTrans (mul_comm _ _)
  have small : Γ ⊢[PRAAx] RationalValueBounds.upper (qnormSq (ap2 F k x)) (qnormSq (ap2 G j y)) one (unit (t+t)) := by
    apply RationalValueBounds.upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive H) (unit_positive H))
      (RationalValueBounds.upper_of_radius _ _ _ _ squareScalar)
    apply le_of_eq_add (d := zero)
    apply deriveNat
    have eq := natEq bit
    ipra_simps
    rw [eq]
    ring
  have upper := RationalValueBounds.upper_order_right _ _ _ _ _ small realBound
  have extracted := GaussianSquaredNormUpper.bound_of_dyadic_squared_upper _ (squaredTolerance A Z) A Z t hZ
    (GaussianRationalMetric.squared_tolerance_represents A Z hZ) upper
  have complexBound : Γ ⊢[PRAAx] bounded (ap2 F k x) ((S*P+T)*U+two*T*P) Z :=
    GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ hZ hU) hZ
      (le_of_eq_add (d := zero) (by dsimp only [A,Z]; ipra_ring)) extracted
  have near := distance_symmetric _ _ _ _ (positive_product _ _ hU hP) (later_observations F x k p t hf hk)
  have close : Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 F k x) (T*(P+U)) Z :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hP) hZ
      (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring)) near
  have total := distance_triangle_same _ _ qzero _ _ Z hZ close
    ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hZ).iffMpr complexBound)
  have point := (GaussianReconstructionRoots.distance_zero_iff _ _ _ hZ).iffMp total
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ hZ hZ
    (le_of_eq_add (d := (T*P)*Z) (by dsimp only [Z,P,U]; ipra_ring)) point

theorem original_norm_transfer (F G : PR 2) (x y p S T : PTm n)
    (hT : Γ ⊢[PRAAx] le one T) (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (he : Γ ⊢[PRAAx] crossEquivalent (squareF F) (squareF G) (squareData F x) (squareData G y))
    (hb : Γ ⊢[PRAAx] bounded (ap2 G p y) S T) : Γ ⊢[PRAAx]
    bounded (ap2 F p x) (S*unit p+two*T) (T*unit p) := by
  let a := ap2 F p x
  let A := S*unit p+two*T
  let D := T*unit p
  let t := GaussianRationalSlackRemoval.precision (qsub a qzero) A D (num 4)
  have hD := positive_product _ _ hT (unit_positive p)
  have raw := cofinal_bound F G x y p S T t hT hf hg he hb
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMp
    (GaussianRationalSlackRemoval.slack_removal_at (qsub a qzero) A D (num 4) hD
      ((GaussianReconstructionRoots.distance_zero_iff _ _ _ (positive_product _ _ hD (unit_positive t))).iffMpr raw))

theorem actual_equal_square_names_norm_radius_transfer_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 4) ⋏ (pointCN F (var 0) ⋏ (pointCN G (var 1) ⋏
      (crossEquivalent (squareF F) (squareF G) (squareData F (var 0)) (squareData G (var 1)) ⋏
        bounded (ap2 G (var 2) (var 1)) (var 3) (var 4))))) ⟶
      bounded (ap2 F (var 2) (var 0)) (var 3*unit (var 2)+two*var 4) (var 4*unit (var 2))) :=
  closeUniv 5 (.impI (original_norm_transfer F G _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerVerticalNormTransfer
