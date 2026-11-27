import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.NamedIncrements.GaussianNamedIncrementDifferenceQuotient

/-!
# Comparison with a frozen coefficient for a named increment

The frozen endpoints and increment may be read from separate programs.
An exact rational factorization at that reading yields an explicit error
at the observation clock of the original normalized quotient.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianNamedIncrementFrozenCoefficient

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianNameEquivalence (cross_to_diagonal diagonal_at)
open GaussianNameRingLaws (oneF one_at three multiply_sample_error)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (canonical qmul)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "RF" => GaussianNameReciprocal.nameF
local notation "rd" => GaussianNameReciprocal.nameData
local notation "DF" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "QF" => GaussianNamedIncrementDifferenceQuotient.nameF
local notation "qd" => GaussianNamedIncrementDifferenceQuotient.data
local notation "R" => GaussianNameReciprocal.R

def inverseCost (K : PR 2) (z a : PTm n) : PTm n :=
  R a*num 8+((multiplyModulus (RF K) K (rd a z) z+one)+two)

def cost (F G K : PR 2) (x y z a H : PTm n) : PTm n :=
  ((multiplyModulus (RF K) (DF F G) (rd a z) (dd x y)+one)+R a*(num 6+(three+three)))+
    H*inverseCost K z a

ipra_subst inverseCost [one, two]

ipra_subst cost [three, one, two]

theorem inverse_at_frozen_increment (K : PR 2) (q z a J : PTm n)
    (hk : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z)
    (hj : Γ ⊢[PRAAx] distanceBounded (ap2 K q z) J (num 8) (unit q)) : Γ ⊢[PRAAx]
    distanceBounded (qmul (ap2 (RF K) q (rd a z)) J) qone (inverseCost K z a) (unit q) := by
  let I := RF K
  let i := rd a z
  let W := multiplyF I K
  let w := multiplyData I K i z
  have hq := unit_positive (Γ := Γ) q
  have hi := GaussianNameReciprocal.name_fast K a z hk.andE₁ hk.andE₂
  have normalized := multiply_sample_error I K i z q hi hk.andE₁
  have inverseCross := GaussianNameReciprocal.product_one_left K a z hk.andE₁ hk.andE₂
  have oneDistance : Γ ⊢[PRAAx] distanceBounded (ap2 W q w) qone two (unit q) :=
    distance_congr (.eqRefl _) (one_at q z) (.eqRefl _) (.eqRefl _)
      (diagonal_at W oneF w z q (cross_to_diagonal W oneF w z inverseCross))
  have actualIncrement := distance_triangle_same _ _ _ _ _ _ hq
    (distance_symmetric _ _ _ _ hq normalized) oneDistance
  have frozenIncrement := GaussianNamedDifferenceQuotient.scale_distance (ap2 I q i) _ _ (R a) (num 8) (unit q) hq
    (GaussianNamedIncrementDifferenceQuotient.inverse_sample_bound K a z q hk)
    (distance_symmetric _ _ _ _ hq hj)
  exact distance_triangle_same _ _ _ _ _ _ hq frozenIncrement actualIncrement

theorem coefficient_at (F G K : PR 2) (q x y z a u v J T H : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianNamedIncrementDifferenceQuotient.input F G K x y z a)
    (hT : Γ ⊢[PRAAx] canonical T) (hH : Γ ⊢[PRAAx] bounded T H one)
    (e : Γ ⊢[PRAAx] qsub u v ≐ qmul J T)
    (hu : Γ ⊢[PRAAx] distanceBounded (ap2 F q x) u three (unit q))
    (hv : Γ ⊢[PRAAx] distanceBounded (ap2 G q y) v three (unit q))
    (hj : Γ ⊢[PRAAx] distanceBounded (ap2 K q z) J (num 8) (unit q)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (QF F G K) q (qd F G K x y z a)) T (cost F G K x y z a H) (unit q) := by
  let inv := ap2 (RF K) q (rd a z)
  have hq := unit_positive (Γ := Γ) q
  have hf := hs.andE₁
  have hg := hs.andE₂.andE₁
  have hk := hs.andE₂.andE₂
  have hi := GaussianNameReciprocal.name_fast K a z hk.andE₁ hk.andE₂
  have hd := GaussianNamedDifference.name_regular F G x y hf hg
  have named := multiply_sample_error (RF K) (DF F G) (rd a z) (dd x y) q hi hd
  have rawDifference := distance_triangle_same _ _ _ _ _ _ hq
    (GaussianNamedDifference.sample_error F G x y q hf hg)
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hq hu hv)
  have freeze := GaussianNamedDifferenceQuotient.scale_distance inv _ _ (R a) _ (unit q) hq
    (GaussianNamedIncrementDifferenceQuotient.inverse_sample_bound K a z q hk) rawDifference
  have factorized : Γ ⊢[PRAAx] qmul inv (qsub u v) ≐ qmul T (qmul inv J) :=
    (qmul_congr (.eqRefl _) e).eqTrans
      ((qmul_associative inv J T).eqSymm.eqTrans (qmul_commutative _ _))
  have unitError := GaussianNamedDifferenceQuotient.scale_distance T _ _ H (inverseCost K z a) (unit q) hq hH
    (inverse_at_frozen_increment K q z a J hk hj)
  have last := distance_congr factorized.eqSymm (qmul_one_right T hT) (.eqRefl _) (.eqRefl _) unitError
  exact distance_triangle_same _ _ _ _ _ _ hq
    (distance_triangle_same _ _ _ _ _ _ hq named freeze) last

theorem actual_named_increment_frozen_coefficient_closed (F G K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      ((GaussianNamedIncrementDifferenceQuotient.input F G K (var 1) (var 2) (var 3) (var 4) ⋏
        (canonical (var 8) ⋏ (bounded (var 8) (var 9) one ⋏
        ((qsub (var 5) (var 6) ≐ qmul (var 7) (var 8)) ⋏
        (distanceBounded (ap2 F (var 0) (var 1)) (var 5) three (unit (var 0)) ⋏
        (distanceBounded (ap2 G (var 0) (var 2)) (var 6) three (unit (var 0)) ⋏
         distanceBounded (ap2 K (var 0) (var 3)) (var 7) (num 8) (unit (var 0)))))))) ⟶
      distanceBounded (ap2 (QF F G K) (var 0) (qd F G K (var 1) (var 2) (var 3) (var 4)))
        (var 8) (cost F G K (var 1) (var 2) (var 3) (var 4) (var 9)) (unit (var 0))) :=
  closeUniv 10 (.impI (coefficient_at F G K _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedIncrementFrozenCoefficient
