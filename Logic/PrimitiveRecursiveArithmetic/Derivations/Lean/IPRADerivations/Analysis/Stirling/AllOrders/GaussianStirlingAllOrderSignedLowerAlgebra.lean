import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderLogTruncation
import IPRADerivations.Analysis.Stirling.GaussianStirlingOddCoefficients
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalNaturalScale

/-!
# Cancellation of the literal sign and denominator

The sign of the first omitted coefficient is (-1)^m. Multiplying
the fixed signed scale by that sign and by its denominator returns
the actual Gaussian rational unit.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSignedLowerAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (num)
open LeanProofs.IPRA.Foundations.NumeralPrimes (num_le)
open BernoulliBounds (zint toZ_zint)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalReciprocal (qone)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianStirlingAllOrderTruncationAlgebra (signedScale)
open GaussianStirlingAllOrderTruncationCoefficients (sign scaleCode)
open GaussianStirlingOddCoefficients (fraction_embed)
open RationalAlgebra (multiply_congr)
open RationalArithmetic (multiply multiply_guard)
open RationalFiniteSum (canonical_equal)
open RationalGaussianEmbedding (embed embed_multiply embed_one)
open RationalGaussianRealPart (embed_congr)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNonnegativePowers (fraction_multiply)
open RationalNormalForm (normalize_well_formed)
open RationalRepresentations (represents_multiply)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def orientationCode (m : ℕ) : PTm n := normalize (zint (sign m)) one
def orientationPoint (m : ℕ) : PTm n := embed (orientationCode m)

@[simp] theorem subst_orientationPoint {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) :
    Syn.subst σ (orientationPoint m : PTm n) = (orientationPoint m : PTm l) := by
  simp [orientationPoint,orientationCode,zint,one]

theorem denominator_positive (m : ℕ) : Γ ⊢[PRAAx] le one (num (2*m+2) : PTm n) :=
  num_le (by omega : 1≤2*m+2)

private theorem orientation_scalar (m : ℕ) :
    Γ ⊢[PRAAx] multiply (orientationCode m : PTm n) (scaleCode m) ≐ fraction one (num (2*m+2)) := by
  let D : PTm n := num (2*m+2)
  let z : ZT n := zint (sign m)
  have hD := denominator_positive (Γ := Γ) m
  have hDD := positive_product _ _ (le_refl one) hD
  have e1 := normalize_preserves_value (Γ := Γ) z one (le_refl one)
  have e2 := normalize_preserves_value (Γ := Γ) z D hD
  have prod := represents_multiply _ _ _ _ _ _ e1 e2
  apply canonical_equal _ _ _ _ _ _ (multiply_guard _ _) (normalize_well_formed _ _ hD)
    prod (fraction_represents _ _ hD) hDD hD
  have self : sign m * sign m = 1 := by
    unfold sign
    rw [← mul_pow]
    norm_num
  have sq := congrArg (fun x : ℤ => (x : Groth (Q Γ))) self
  push_cast at sq
  apply ZT.derive
  simp only [z,ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint]
  dsimp only [D]
  ipra_simps
  rw [sq]
  ring

private theorem inverse_scalar (m : ℕ) :
    Γ ⊢[PRAAx] multiply (fraction (num (2*m+2)) one) (fraction one (num (2*m+2))) ≐ (fraction one one : PTm n) := by
  let D : PTm n := num (2*m+2)
  have hD := denominator_positive (Γ := Γ) m
  have hp := positive_product _ _ (le_refl one) hD
  refine (fraction_multiply D one one D (le_refl one) hD).eqTrans ?_
  apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hp)
    (normalize_well_formed _ _ (le_refl one)) (fraction_represents _ _ hp)
    (fraction_represents _ _ (le_refl one)) hp (le_refl one)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  dsimp only [D]
  ipra_simps
  ring

theorem cancel_orientation_and_denominator (m : ℕ) : Γ ⊢[PRAAx]
    qmul (qmul (naturalPoint (num (2*m+2))) (orientationPoint m)) (signedScale m) ≐ (qone : PTm n) := by
  let D : PTm n := num (2*m+2)
  let x := fraction D one
  let a := orientationCode (n := n) m
  let b := scaleCode (n := n) m
  have nx : Γ ⊢[PRAAx] naturalPoint D ≐ embed x := (fraction_embed D one (le_refl one)).eqSymm
  have undoInner := (embed_multiply (Γ := Γ) a b).eqSymm.eqTrans (embed_congr (orientation_scalar m))
  exact (qmul_associative _ _ _).eqTrans ((qmul_congr nx undoInner).eqTrans
    ((embed_multiply _ _).eqSymm.eqTrans ((embed_congr (inverse_scalar m)).eqTrans embed_one)))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderSignedLowerAlgebra
