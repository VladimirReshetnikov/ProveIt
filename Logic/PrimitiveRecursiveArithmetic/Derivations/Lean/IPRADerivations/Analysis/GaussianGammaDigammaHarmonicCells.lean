import IPRADerivations.Analysis.GaussianGammaDigammaHarmonicTrapezoid
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsOrder

/-!
# Right and trapezoid rectangles for one harmonic cell

On a common factorial mesh, the cell for a/b to a/b+1 is between
the right endpoint reciprocal and the average endpoint reciprocals.
The comparisons refer to the actual canonical rational codes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaHarmonicCells

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qzero positive_product scalar_congr)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open Products (fact)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalGaussianEmbedding (embed)
open RationalHarmonicInterval (common common_value numerator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def cell (a c Q L : PTm n) : PTm n := embed (common a c Q L)
def halfReciprocal (a b : PTm n) : PTm n := fraction b (two*a)

@[simp] theorem subst_cell {m : ℕ} (σ : Fin n → PTm m) (a c Q L : PTm n) :
    Syn.subst σ (cell a c Q L) = cell (Syn.subst σ a) (Syn.subst σ c) (Syn.subst σ Q) (Syn.subst σ L) := by simp [cell]

@[simp] theorem subst_halfReciprocal {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (halfReciprocal a b) = halfReciprocal (Syn.subst σ a) (Syn.subst σ b) := by simp [halfReciprocal,two]

theorem point_fraction_represents (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (fraction a b)) (ZT.ofNat a) b :=
  scalar_congr (GaussianStirlingMultiplicativeBoundsOrder.fraction_real_part a b hb).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEuclideanDistanceName.fraction_represents a b hb)

theorem cell_represents (a c Q L : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (fstT (cell a c Q L)) (numerator a c Q L) (fact L) := by
  apply scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (RationalGaussianEmbedding.embed_from_representation _ _ _ (common_value a c Q L)).andE₁
  apply ZT.derive
  simp [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code]

theorem half_pair (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qadd (halfReciprocal a b) (halfReciprocal a b) ≐ fraction b a := by
  have h := positive_product two a (le_succ_self one) ha
  have f := GaussianEulerPositivePowerChartCorrectedImage.fraction_sum b (two*a) b (two*a) h h
  exact f.eqTrans (GaussianStirlingRationalTelescopers.fraction_same _ _ b a (positive_product _ _ h h) ha (by ipra_ring))

theorem trapezoid_exact (a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qadd (halfReciprocal a b) (halfReciprocal (a+b) b) ≐
      fraction (b*(two*a+b)) (two*a*(a+b)) := by
  have hap := le_trans ha (le_add_right a b)
  have h := positive_product two a (le_succ_self one) ha
  have hp := positive_product two (a+b) (le_succ_self one) hap
  have f := GaussianEulerPositivePowerChartCorrectedImage.fraction_sum b (two*a) b (two*(a+b)) h hp
  exact f.eqTrans (GaussianStirlingRationalTelescopers.fraction_same _ _ _ _ (positive_product _ _ h hp)
    (positive_product _ _ h hap) (by ipra_ring))

theorem right_rectangle (a b Q L : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hQ : Γ ⊢[PRAAx] le one Q) (hL : Γ ⊢[PRAAx] le (Q*(a+b)) L) :
    Γ ⊢[PRAAx] rationalLE (fstT (fraction b (a+b))) (fstT (cell (a+b) a Q L)) := by
  have bound := (GaussianHarmonicIntervalLinearRemainder.rectangles a b Q L ha hQ hL).andE₁
  have hF := GammaEulerMesh.factorial_positive (Γ := Γ) L
  have hp := le_trans ha (le_add_right a b)
  refine RationalArithmetic.order_of_representations _ _ (ZT.ofNat b) (numerator (a+b) a Q L) (a+b) (fact L)
    (point_fraction_represents b (a+b) hp) (cell_represents _ _ _ _) hp hF ?_
  apply zle_of_toZ (monus ((a+b)*S (Q*(a+b)) (fact L)) ((a+b)*S (Q*a) (fact L)+b*fact L))
  have e := natEq (eq_add_of_le bound)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  ipra_simps
  linear_combination -e

theorem trapezoid (a b Q L : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] rationalLE (fstT (cell (a+b) a Q L)) (fstT (qadd (halfReciprocal a b) (halfReciprocal (a+b) b))) := by
  let D := two*a*(a+b)
  let A := b*(two*a+b)
  let F := fact L
  have hF := GammaEulerMesh.factorial_positive (Γ := Γ) L
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ (le_succ_self one) ha)
    (le_trans ha (le_add_right a b))
  have bound := GaussianGammaDigammaHarmonicTrapezoid.factorial_trapezoid a b Q L hQ
  refine rationalLE_congr (.eqRefl _) (congrFst (trapezoid_exact a b ha)).eqSymm ?_
  refine RationalArithmetic.order_of_representations _ _ (numerator (a+b) a Q L) (ZT.ofNat A) F D
    (cell_represents _ _ _ _) (point_fraction_represents A D hD) hF hD ?_
  apply zle_of_toZ (monus (D*S (Q*a) F+A*F) (D*S (Q*(a+b)) F))
  have e := natEq (eq_add_of_le bound)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  dsimp only [D,A,F]
  ipra_simps
  linear_combination -e

theorem cell_zero (a Q L : PTm n) : Γ ⊢[PRAAx] cell a a Q L ≐ qzero :=
  (GaussianPositiveRationalLogarithmProperness.common_difference a a Q L).eqSymm.eqTrans (GaussianCoefficientNormOrder.qsub_self _)

theorem chain (a c d Q L : PTm n) : Γ ⊢[PRAAx] qadd (cell c a Q L) (cell d c Q L) ≐ cell d a Q L := by
  let X := embed (GaussianPositiveRationalLogarithmProperness.commonLog d Q L)
  let Y := embed (GaussianPositiveRationalLogarithmProperness.commonLog c Q L)
  let Z := embed (GaussianPositiveRationalLogarithmProperness.commonLog a Q L)
  exact (qadd_congr (GaussianPositiveRationalLogarithmProperness.common_difference c a Q L).eqSymm
    (GaussianPositiveRationalLogarithmProperness.common_difference d c Q L).eqSymm).eqTrans
      ((GaussianReciprocalHorner.qadd_commutative (qsub Y Z) (qsub X Y)).eqTrans
        ((GaussianReconstructionRoots.difference_chain X Y Z).eqTrans
          (GaussianPositiveRationalLogarithmProperness.common_difference d a Q L)))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaHarmonicCells
