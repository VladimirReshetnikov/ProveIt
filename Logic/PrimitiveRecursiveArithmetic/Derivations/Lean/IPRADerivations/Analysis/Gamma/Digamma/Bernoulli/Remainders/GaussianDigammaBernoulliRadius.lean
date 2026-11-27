import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.Remainders.GaussianDigammaBernoulliCoefficients
import IPRADerivations.Analysis.Stirling.AllOrders.Logarithms.GaussianStirlingAllOrderSharpRadiusBridge

/-!
# Exact magnitude of the first omitted digamma term

The digamma and Stirling primitives have consecutive inverse powers
and the same centered Bernoulli mean. The existing positive
Stirling radius gives the exact positive digamma radius.
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliRadius

open_ipra
open BernoulliBounds (bden bden_pos)
open GaussianDigammaBernoulliCoefficients (coefficientNumerator)
open GaussianDigammaBernoulliRecurrence (exponent weightedPrimitive)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianStirlingAllOrderLogRateTransport (upperPoint)
open GaussianStirlingAllOrderPowerIntegralMeshCells (primitive)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open GaussianStirlingAllOrderPanelDerivative (signedMean)
open GaussianStirlingAllOrderSignedBoundsTransport (scaled_cap_exact)
open GaussianStirlingNames (source)
open RationalAlgebra (multiply_associative multiply_commutative multiply_congr)
open RationalArithmetic (multiply)
open RationalFiniteSum (canonical_equal)
open RationalGaussianEmbedding (embed embed_multiply)
open RationalGaussianRealPart (embed_congr)
open RationalNonnegativePowers (fraction_multiply fraction_congr)
open RationalNormalForm (normalize_well_formed)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def absoluteCoefficient (m : ℕ) : ℕ := (coefficientNumerator m).natAbs
def radiusNumerator (m : ℕ) (B : PTm n) : PTm n := num (absoluteCoefficient m)*power (2*m+2) B
def radiusDenominator (m : ℕ) (A : PTm n) : PTm n := num (bden (2*m+2))*power (2*m+2) A

theorem absolute_coefficient_step (m : ℕ) :
    absoluteCoefficient m = (2*m+1)*GaussianStirlingAllOrderSharpRadius.absoluteCoefficient m := by
  unfold absoluteCoefficient GaussianStirlingAllOrderSharpRadius.absoluteCoefficient
    coefficientNumerator GaussianStirlingAllOrderTruncationCoefficients.coefficientNumerator
  rw [Nat.factorial_succ (2*m)]
  simp only [Int.natAbs_mul,Int.natAbs_natCast,Nat.mul_assoc]

theorem absolute_coefficient_value (m : ℕ) :
    (absoluteCoefficient m : ℚ)/(bden (2*m+2) : ℚ) =
      |(((2*m+2).factorial : ℚ)*BernoulliCoefficients.bc (2*m+2) 0)/(2*m+2)| := by
  unfold absoluteCoefficient
  rw [←Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs,←GaussianDigammaBernoulliCoefficients.bernoulli_coefficient,
    abs_div,abs_of_pos (show (0 : ℚ)<bden (2*m+2) by exact_mod_cast bden_pos (2*m+2))]

theorem radius_denominator_positive (m : ℕ) (A : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (radiusDenominator m A) :=
  positive_product _ _
    (Foundations.NumeralPrimes.num_le (bden_pos _)) (GaussianFactorBudget.power_positive _ _ hA)

private theorem degree_positive (k m : ℕ) (hk : 0<k) : Γ ⊢[PRAAx] le one (num (2*m+k) : PTm n) :=
  Foundations.NumeralPrimes.num_le (a := 1) (by omega)

private theorem power_step (m : ℕ) (A : PTm n) :
    Γ ⊢[PRAAx] power (2*m+2) A ≐ power (2*m+1) A*A := by
  have e : Γ ⊢[PRAAx] (num (2*m+2) : PTm n) ≐ succ (num (2*m+1)) := by
    apply deriveNat
    ipra_simps
    push_cast
    ring
  exact (congrAp2 powF e (.eqRefl _)).eqTrans (pw_succ _ _)

private def bridgeFraction (m : ℕ) (A B : PTm n) : PTm n :=
  fraction (num (2*m+1)*B) (num (2*m+2)*A)

private theorem primitive_bridge (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] multiply (bridgeFraction m A B) (primitive (2*m+2) A B) ≐ primitive (exponent m) A B := by
  let j : PTm n := num (2*m+1)
  let d : PTm n := num (2*m+2)
  let U := power (2*m+1) B
  let V := power (2*m+1) A
  have hj := degree_positive (Γ := Γ) 1 m (by omega)
  have hd := degree_positive (Γ := Γ) 2 m (by omega)
  have hV := GaussianFactorBudget.power_positive (Γ := Γ) A (num (2*m+1)) hA
  have hD := GaussianFactorBudget.power_positive (Γ := Γ) A (num (2*m+2)) hA
  have h := fraction_multiply (j*B) (d*A) U (j*V) (positive_product _ _ hd hA)
    (positive_product _ _ hj hV)
  have he : Γ ⊢[PRAAx] fraction ((j*B)*U) ((d*A)*(j*V)) ≐ fraction (power (2*m+2) B) (d*power (2*m+2) A) := by
    have he₁ := positive_product _ _ (positive_product _ _ hd hA) (positive_product _ _ hj hV)
    have he₂ := positive_product _ _ hd hD
    apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ he₁) (normalize_well_formed _ _ he₂)
      (fraction_represents _ _ he₁) (fraction_represents _ _ he₂) he₁ he₂
    apply ZT.derive
    have ea := natEq (power_step (Γ := Γ) m A)
    have eb := natEq (power_step (Γ := Γ) m B)
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul] at ea eb ⊢
    dsimp only [U,V,j,d,power] at ea eb ⊢
    rw [ea,eb]
    ring
  have oldDegree : 2*m+2-1=2*m+1 := by omega
  have newDegree : exponent m-1=2*m+2 := by unfold exponent; omega
  simpa only [bridgeFraction,primitive,oldDegree,newDegree,j,d,U,V] using h.eqTrans he

private theorem weighted_bridge (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] weightedPrimitive m A B ≐
      qmul (embed (bridgeFraction m A B)) (GaussianStirlingAllOrderPanelPartsNames.weightedPrimitive m A B) := by
  let r := bridgeFraction m A B
  let c := signedMean (n := n) (m+1)
  let p := primitive (2*m+2) A B
  have e : Γ ⊢[PRAAx] multiply r (multiply c p) ≐ multiply c (primitive (exponent m) A B) :=
    (multiply_associative _ _ _).eqSymm.eqTrans
      ((multiply_congr (multiply_commutative _ _) (.eqRefl _)).eqTrans
        ((multiply_associative _ _ _).eqTrans (multiply_congr (.eqRefl _) (primitive_bridge m A B hA))))
  exact (embed_congr e).eqSymm.eqTrans (embed_multiply _ _)

private theorem bridge_scaled (m : ℕ) (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] qmul (embed (bridgeFraction m A B)) (naturalPoint (num (2*m+2))) ≐
      embed (fraction (num (2*m+1)*B) A) := by
  let j : PTm n := num (2*m+1)
  let d : PTm n := num (2*m+2)
  let R := j*B
  have hd := degree_positive (Γ := Γ) 2 m (by omega)
  have hD := positive_product _ _ hd hA
  have hE := positive_product _ _ hD (le_refl one)
  have e : Γ ⊢[PRAAx] multiply (fraction R (d*A)) (fraction d one) ≐ fraction R A := by
    refine (fraction_multiply _ _ _ _ hD (le_refl one)).eqTrans ?_
    apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hE) (normalize_well_formed _ _ hA)
      (fraction_represents _ _ hE) (fraction_represents _ _ hA) hE hA
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul,IPRA.Q.mk_one,map_one]
    ring
  have q := GaussianEulerDecayOrder.fraction_embedding (Γ := Γ) d one (le_refl one)
  exact (qmul_congr (.eqRefl _) q.eqSymm).eqTrans ((embed_multiply _ _).eqSymm.eqTrans (embed_congr e))

theorem weighted_primitive_radius (m : ℕ) (A B : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] weightedPrimitive m A B ≐ upperPoint (radiusNumerator m B) (radiusDenominator m A) := by
  let J : PTm n := num (2*m+1)
  let C : PTm n := num (GaussianStirlingAllOrderSharpRadius.absoluteCoefficient m)
  let D : PTm n := num (bden (2*m+2))
  let U := power (2*m+1) B
  let V := power (2*m+1) A
  let oldN := C*U
  let oldD := D*V
  have hD := GaussianStirlingAllOrderSharpRadius.radius_denominator_positive m A hs.andE₁
  have original := GaussianStirlingAllOrderSharpRadiusBridge.cap_exact m A B zero hs
  have formula : Γ ⊢[PRAAx] weightedPrimitive m A B ≐ qmul (embed (fraction (J*B) A)) (embed (fraction oldN oldD)) :=
    (weighted_bridge m A B hs.andE₁).eqTrans
      ((qmul_congr (.eqRefl _) (scaled_cap_exact m A B hs.andE₁).eqSymm).eqTrans
        ((qmul_associative _ _ _).eqSymm.eqTrans
          (qmul_congr (bridge_scaled m A B hs.andE₁) original)))
  have c : Γ ⊢[PRAAx] num (absoluteCoefficient m) ≐ J*C := by
    unfold J C
    apply deriveNat
    ipra_simps
    rw [absolute_coefficient_step]
    push_cast
    ring
  have numEq : Γ ⊢[PRAAx] (J*B)*oldN ≐ radiusNumerator m B :=
    (by unfold oldN U; ipra_ring : Γ ⊢[PRAAx] (J*B)*oldN ≐ (J*C)*(power (2*m+1) B*B)).eqTrans
      (congrMul c.eqSymm (power_step m B).eqSymm)
  have denEq : Γ ⊢[PRAAx] A*oldD ≐ radiusDenominator m A :=
    (by unfold oldD V; ipra_ring : Γ ⊢[PRAAx] A*oldD ≐ D*(power (2*m+1) A*A)).eqTrans
      (congrMul (.eqRefl _) (power_step m A).eqSymm)
  exact formula.eqTrans ((embed_multiply _ _).eqSymm.eqTrans
    (embed_congr ((fraction_multiply _ _ _ _ hs.andE₁ hD).eqTrans (fraction_congr numEq denEq))))

end LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliRadius
