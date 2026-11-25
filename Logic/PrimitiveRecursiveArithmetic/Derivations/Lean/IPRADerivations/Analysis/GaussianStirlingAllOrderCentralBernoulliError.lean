import IPRADerivations.Analysis.GaussianStirlingAllOrderCentralDerivativeBinding
import IPRADerivations.Analysis.GaussianStirlingAllOrderDiscreteParts
import IPRADerivations.Analysis.RationalRepresentedUpper
import IPRADerivations.Analysis.RationalGaussianNameEmbedding

/-!
# The actual centered Bernoulli grid has a second-order curvature error

The scaled second difference is taken on the literal canonical profile
samples. Its exact signed row remainder is the cleared central Taylor
defect and has an explicit error of order M^(-2).
-/

set_option autoImplicit false
set_option maxHeartbeats 1050000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCentralBernoulliError

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderCenteredBernoulli
  (factor sample numerator denominator sample_value denominator_positive)
open GaussianStirlingAllOrderPanelDerivative (secondSample secondNumerator)
open GaussianStirlingAllOrderDiscreteParts (sub secondDifference)
open GaussianStirlingAllOrderCentralTaylorBound (radiusCoefficient curvatureNumerator)
open GaussianStirlingAllOrderCentralDerivativeBinding (actual_curvature_numerator)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product scalar_congr scalar_cancel scalar_add_same)
open BernoulliBounds (pv bint bden bden_pos zint toZ_zint natAbs_cast_of_nonneg natAbs_cast_of_neg)
open RationalArithmetic (multiply represents)
open RationalRepresentations (represents_negative represents_multiply)
open RationalIntegerNormalization (normalize normalize_preserves_value)
open RationalNormalForm (normalize_well_formed)
open RationalValueBounds (upper radius radius_of_upper)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def degree (m : ℕ) : ℕ := 2*(m+1)

def lowDen (m : ℕ) (M : PTm n) : PTm n := num (bden (degree m))*pw M (num (2*m))

def scaledNumerator (m : ℕ) (p M : PTm n) : ZT n :=
  zint (factor (m+1))*(pv (bint (degree m)) (p+one) M+
    pv (bint (degree m)) (monus p one) M-ZT.ofNat two*pv (bint (degree m)) p M)

def curvatureNumerator (m : ℕ) (p M : PTm n) : ZT n :=
  zint (factor (m+1))*GaussianStirlingAllOrderCentralTaylorBound.curvatureNumerator (degree m) (bint (degree m)) p M

def scaledSecond (m : ℕ) (p M : PTm n) : PTm n :=
  multiply (fraction (M*M) one)
    (secondDifference (sample (m+1) (monus p one) M) (sample (m+1) p M) (sample (m+1) (p+one) M))

def radiusNumerator (m : ℕ) : PTm n := num ((factor (m+1)).natAbs*radiusCoefficient (degree m) (bint (degree m)))
def radiusDenominator (m : ℕ) (M : PTm n) : PTm n := num (bden (degree m))*(M*M)

private theorem low_positive (m : ℕ) (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (lowDen m M) :=
  positive_product _ _ (Foundations.NumeralPrimes.num_le (a := 1) (bden_pos (degree m)))
    (GaussianFactorBudget.power_positive _ _ hM)

theorem radius_denominator_positive (m : ℕ) (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (radiusDenominator m M) :=
  positive_product _ _ (Foundations.NumeralPrimes.num_le (a := 1) (bden_pos (degree m))) (positive_product _ _ hM hM)

private theorem den_relation (m : ℕ) (M : PTm n) :
    Γ ⊢[PRAAx] denominator (m+1) M ≐ lowDen m M*(M*M) := by
  apply deriveNat
  simp only [denominator,lowDen,degree,IPRA.Q.mk_mul,map_mul,AnalyticNumberTheory.RobinThreePos.pw_lit]
  rw [show 2*(m+1)=2*m+2 by omega,pow_add]
  ring

theorem scaled_value (m : ℕ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] represents (scaledSecond m p M) (scaledNumerator m p M) (lowDen m M) := by
  let D := denominator (m+1) M
  let U := sample (m+1) (p+one) M
  let V := sample (m+1) p M
  let W := sample (m+1) (monus p one) M
  let u := numerator (m+1) (p+one) M
  let v := numerator (m+1) p M
  let w := numerator (m+1) (monus p one) M
  have hD := denominator_positive (m+1) M hM
  have hv := sample_value (m+1) p M hM
  have xa := scalar_add_same U W u w D hD (sample_value (m+1) (p+one) M hM)
    (sample_value (m+1) (monus p one) M hM)
  have xb := represents_negative _ _ _ (scalar_add_same V V v v D hD hv hv)
  have xc := scalar_add_same _ _ _ _ D hD xa xb
  have xp := represents_multiply _ _ _ _ _ D (fraction_represents (M*M) one (le_refl one)) xc
  apply scalar_cancel _ _ _ (M*M) (positive_product _ _ hM hM)
  refine scalar_congr (.eqRefl _) ?_ ((one_mul D).eqTrans (den_relation m M)) xp
  apply ZT.derive
  dsimp only [u,v,w,numerator,scaledNumerator,degree]
  simp only [ZT.toZ_add,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_mul,ZT.toZ_ofNat,toZ_zint]
  ipra_simps
  ring

theorem exact_derivative_value (m : ℕ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] represents (secondSample m p M) (curvatureNumerator m p M) (lowDen m M) := by
  let S := normalize (curvatureNumerator m p M) (lowDen m M)
  have hD := low_positive m M hM
  have hB := denominator_positive m M hM
  have e : Γ ⊢[PRAAx] S ≐ secondSample m p M := by
    apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
      (normalize_well_formed _ _ hD) (normalize_well_formed _ _ hB)
      (normalize_preserves_value _ _ hD) (normalize_preserves_value _ _ hB) hD hB
    have hd : degree m = 2*m+2 := by unfold degree; omega
    have h := ZT.toZ_eq (actual_curvature_numerator (Γ := Γ) (2*m) p M)
    apply ZT.derive (u := curvatureNumerator m p M*ZT.ofNat (denominator m M))
      (v := secondNumerator m p M*ZT.ofNat (lowDen m M))
    dsimp only [curvatureNumerator,secondNumerator,denominator,lowDen]
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul,toZ_zint] at h ⊢
    rw [hd]
    linear_combination ((factor (m+1) : Groth (IPRA.Q Γ))*𝔞(pw M (num (2*m))))*h
  exact scalar_congr e (ZT.derive rfl) (.eqRefl _) (normalize_preserves_value _ _ hD)

private theorem depth_relation (m : ℕ) (M : PTm n) (hm : 0<m) :
    Γ ⊢[PRAAx] lowDen m M ≐ radiusDenominator m M*pw M (num (degree m-4)) := by
  apply deriveNat
  simp only [lowDen,radiusDenominator,IPRA.Q.mk_mul,map_mul,AnalyticNumberTheory.RobinThreePos.pw_lit]
  have e : 2*m = 2+(degree m-4) := by unfold degree; omega
  rw [e,pow_add]
  ring

private theorem numerator_brackets (m : ℕ) (p M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hlo : Γ ⊢[PRAAx] le one p) (hhi : Γ ⊢[PRAAx] le p M) :
    let w := scaledNumerator m p M-curvatureNumerator m p M
    let e := radiusNumerator m*pw M (num (degree m-4))
    (Γ ⊢[PRAAx] zle w (ZT.ofNat e)) ∧ (Γ ⊢[PRAAx] zle (-ZT.ofNat e) w) := by
  let d := degree m
  let b := bint d
  let f := factor (m+1)
  have hi := GaussianStirlingAllOrderCentralTaylorBound.upper d b p M hM hhi hlo
  have lo := GaussianStirlingAllOrderCentralTaylorBound.lower d b p M hM hhi hlo
  have split :
      ZT.toZ Γ (scaledNumerator m p M-curvatureNumerator m p M) =
        (f : Groth (IPRA.Q Γ))*ZT.toZ Γ (GaussianStirlingAllOrderCentralTaylorBound.defect d b p M) := by
    dsimp only [scaledNumerator,curvatureNumerator,GaussianStirlingAllOrderCentralTaylorBound.defect,f,d,b]
    simp only [ZT.toZ_sub,ZT.toZ_add,ZT.toZ_mul,toZ_zint]
    ring
  by_cases hf : 0≤factor (m+1)
  · constructor
    · apply zle_of_comb ((f.natAbs : Groth (IPRA.Q Γ))*zsl hi)
      · simp only [zsl_def,ZT.toZ_ofNat,ZT.toZ_sub,radiusNumerator]
        ipra_simps
        dsimp only [f,d,b] at split ⊢
        push_cast
        rw [natAbs_cast_of_nonneg hf]
        linear_combination -split
      · exact nn_mul (nn_natCast _) (nn_zsl hi)
    · apply zle_of_comb ((f.natAbs : Groth (IPRA.Q Γ))*zsl lo)
      · simp only [zsl_def,ZT.toZ_ofNat,ZT.toZ_sub,ZT.toZ_neg,radiusNumerator]
        ipra_simps
        dsimp only [f,d,b] at split ⊢
        push_cast
        rw [natAbs_cast_of_nonneg hf]
        linear_combination split
      · exact nn_mul (nn_natCast _) (nn_zsl lo)
  · constructor
    · apply zle_of_comb ((f.natAbs : Groth (IPRA.Q Γ))*zsl lo)
      · simp only [zsl_def,ZT.toZ_ofNat,ZT.toZ_sub,ZT.toZ_neg,radiusNumerator]
        ipra_simps
        dsimp only [f,d,b] at split ⊢
        push_cast
        rw [natAbs_cast_of_neg (lt_of_not_ge hf)]
        linear_combination -split
      · exact nn_mul (nn_natCast _) (nn_zsl lo)
    · apply zle_of_comb ((f.natAbs : Groth (IPRA.Q Γ))*zsl hi)
      · simp only [zsl_def,ZT.toZ_ofNat,ZT.toZ_sub,ZT.toZ_neg,radiusNumerator]
        ipra_simps
        dsimp only [f,d,b] at split ⊢
        push_cast
        rw [natAbs_cast_of_neg (lt_of_not_ge hf)]
        linear_combination split
      · exact nn_mul (nn_natCast _) (nn_zsl hi)

theorem curvature_error (m : ℕ) (p M : PTm n) (hm : 0<m) (hM : Γ ⊢[PRAAx] le one M)
    (hlo : Γ ⊢[PRAAx] le one p) (hhi : Γ ⊢[PRAAx] le p M) :
    Γ ⊢[PRAAx] radius (scaledSecond m p M) (secondSample m p M) (radiusNumerator m) (radiusDenominator m M) := by
  let a := scaledSecond m p M
  let b := secondSample m p M
  let x := scaledNumerator m p M
  let y := curvatureNumerator m p M
  let D := lowDen m M
  let E := radiusDenominator m M
  let N : PTm n := radiusNumerator m
  let Q := pw M (num (degree m-4))
  have hr := numerator_brackets m p M hM hlo hhi
  have ep := natEq (depth_relation (Γ := Γ) m M hm)
  have hD := low_positive m M hM
  have va := scaled_value m p M hM
  have vb := exact_derivative_value m p M hM
  have go₁ : Γ ⊢[PRAAx] upper a b N E := by
    apply RationalRepresentedUpper.from_signed _ _ x y D D N E hD hD va vb
    apply zle_of_comb (𝔞(D)*𝔞(E)*zsl hr.1)
    · simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,zsl_def,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_add,ZT.toZ_sub]
      ipra_simps
      dsimp only [x,y,D,E,N,Q] at ep ⊢
      linear_combination (𝔞(D)*𝔞(N))*ep
    · exact nn_mul (nn_mul (nn_term _) (nn_term _)) (nn_zsl hr.1)
  have go₂ : Γ ⊢[PRAAx] upper b a N E := by
    apply RationalRepresentedUpper.from_signed _ _ y x D D N E hD hD vb va
    apply zle_of_comb (𝔞(D)*𝔞(E)*zsl hr.2)
    · simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,zsl_def,ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_neg]
      ipra_simps
      dsimp only [x,y,D,E,N,Q] at ep ⊢
      linear_combination (𝔞(D)*𝔞(N))*ep
    · exact nn_mul (nn_mul (nn_term _) (nn_term _)) (nn_zsl hr.2)
  exact radius_of_upper _ _ _ _ go₁ go₂

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCentralBernoulliError
