import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.GaussianStirlingAllOrderSignedBounds
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums

/-!
# The literal truncation sign at even and odd orders
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSignedParityAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open BernoulliBounds (zint toZ_zint)
open GaussianRationalMatrixFiniteSums (minusOne negative_as_minusOne)
open GaussianRationalMetric (qnegative)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianStirlingAllOrderSignedBoundsTransport (orientedCap)
open GaussianStirlingAllOrderSignedLowerAlgebra (orientationCode orientationPoint)
open GaussianStirlingAllOrderTruncationAlgebra (correction)
open GaussianStirlingAllOrderTruncationCoefficients (sign)
open RationalArithmetic (negative negative_guard)
open RationalFiniteSum (canonical_equal)
open RationalGaussianEmbedding (embed embed_canonical scalarOne embed_one embed_negative)
open RationalGaussianRealPart (embed_congr)
open RationalIntegerNormalization (normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open RationalRepresentations (represents_negative)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem orientation_even (m : ℕ) (hm : Even m) :
    Γ ⊢[PRAAx] (orientationPoint m : PTm n) ≐ qone := by
  have s : sign m = 1 := by unfold sign; exact hm.neg_one_pow
  have p : Γ ⊢[PRAAx] (orientationCode m : PTm n) ≐ scalarOne := by
    unfold orientationCode scalarOne
    rw [s]
    apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ (le_refl one))
      (normalize_well_formed _ _ (le_refl one)) (normalize_preserves_value _ _ (le_refl one))
      (normalize_preserves_value _ _ (le_refl one)) (le_refl one) (le_refl one)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint]
    ipra_simps
    ring
  exact (embed_congr p).eqTrans embed_one

theorem orientation_odd (m : ℕ) (hm : Odd m) :
    Γ ⊢[PRAAx] (orientationPoint m : PTm n) ≐ minusOne := by
  have s : sign m = -1 := by unfold sign; exact hm.neg_one_pow
  have p : Γ ⊢[PRAAx] (orientationCode m : PTm n) ≐ negative scalarOne := by
    unfold orientationCode
    rw [s]
    have rep := represents_negative (Γ := Γ) _ _ _
      (normalize_preserves_value (ZT.ofNat one) one (le_refl one))
    apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ (le_refl one)) (negative_guard _)
      (normalize_preserves_value _ _ (le_refl one)) rep (le_refl one) (le_refl one)
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_neg,toZ_zint]
    ipra_simps
    ring
  exact (embed_congr p).eqTrans ((embed_negative _).eqTrans (RationalGaussianEmbedding.negative_congr embed_one))

theorem even_cap (m : ℕ) (hm : Even m) (A B : PTm n) :
    Γ ⊢[PRAAx] orientedCap m A B ≐ correction m A B :=
  (qmul_congr (orientation_even m hm) (.eqRefl _)).eqTrans
    ((qmul_commutative _ _).eqTrans (qmul_one_right _ (embed_canonical _)))

theorem odd_cap (m : ℕ) (hm : Odd m) (A B : PTm n) :
    Γ ⊢[PRAAx] orientedCap m A B ≐ qnegative (correction m A B) :=
  (qmul_congr (orientation_odd m hm) (.eqRefl _)).eqTrans (negative_as_minusOne _).eqSymm

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSignedParityAlgebra
