import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalHeadDerivativeJoin
import IPRADerivations.Analysis.Barnes.Growth.GaussianBarnesCanonicalDiskBound
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHeadLipschitz

/-!
# Derivative product rule for the actual Barnes kept prefix

The original prefix multiplies the prefactor by the finite kept head.
For the quantitative product rule the factors are read in the opposite
order, so only the prefactor derivative needs an absolute sample cap.
The exact original prefix quotient is recovered by commutativity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefixDerivativeJoin

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalHead (headData)
open GaussianBarnesCanonicalHeadCorrectionDerivative (point_increment)
open GaussianBarnesCanonicalHeadDerivativeJoin (head_samples_bound)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalValue (prefixF prefixData prefix_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianL1 (norm1 normSq_le_norm1_square)
open GaussianNameArithmetic (add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "DH" => GaussianBarnesCanonicalHeadDerivativeJoin.derivativeF
local notation "dhd" => GaussianBarnesCanonicalHeadDerivativeJoin.derivativeData
local notation "Hcap" => GaussianBarnesCanonicalHead.cap
local notation "Hgain" => GaussianBarnesCanonicalHeadLipschitz.gain
local notation "Pcap" => GaussianBarnesCanonicalDiskBound.prefactorBound
local notation "QF" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data

def derivativeF (DP : PR 2) : PR 2 := GaussianNamedNativeProductDerivativeRate.derivativeF H P DH DP
def derivativeData (DP : PR 2) (z R B d : PTm n) : PTm n :=
  GaussianNamedNativeProductDerivativeRate.derivativeData H P DH DP
    (headData z R B (initial R)) (pd z B) (dhd z B (initial R)) d

def gain (R headGain prefactorGain derivativeCap : PTm n) : PTm n :=
  Hcap R zero (initial R)*prefactorGain + derivativeCap*Hgain R zero (initial R) + Pcap R*headGain

def denominator (R B : PTm n) : PTm n := B*initial R

@[simp] theorem subst_derivativeData {m : ℕ} (σ : Fin n → PTm m) (DP : PR 2) (z R B d : PTm n) :
    Syn.subst σ (derivativeData DP z R B d) =
      derivativeData DP (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ d) := by
  simp [derivativeData,GaussianNamedNativeProductDerivativeRate.derivativeData,headData]

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R headGain prefactorGain derivativeCap : PTm n) :
    Syn.subst σ (gain R headGain prefactorGain derivativeCap) =
      gain (Syn.subst σ R) (Syn.subst σ headGain) (Syn.subst σ prefactorGain) (Syn.subst σ derivativeCap) := by
  simp [gain]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (R B : PTm n) :
    Syn.subst σ (denominator R B) = denominator (Syn.subst σ R) (Syn.subst σ B) := by
  simp [denominator]

theorem regular (DP : PR 2) (z R B d : PTm n) (hs : Γ ⊢[PRAAx] source z R B)
    (hd : Γ ⊢[PRAAx] pointCN DP d) : Γ ⊢[PRAAx] pointCN (derivativeF DP) (derivativeData DP z R B d) :=
  add_fast _ _ _ _
    (multiply_fast _ _ _ _ hd (GaussianBarnesCanonicalHead.regular z R B zero (initial R) hs))
    (multiply_fast _ _ _ _ (GaussianBarnesCanonicalPrefactor.regular z B)
      (GaussianBarnesCanonicalHeadDerivativeJoin.regular z B (initial R)))

theorem prefactor_samples_bound (z R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound P (pd z B) (Pcap R) := by
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh] using hs.shift
  simpa only [sampleBound,Syn.shift,sh,GaussianBarnesCanonicalPrefactor.subst_data,
    GaussianBarnesCanonicalDiskBound.subst_prefactorBound] using
    GaussianBarnesCanonicalDiskBound.prefactor_sample_bound (var 0) (sh z) (sh R) (sh B) hh

theorem head_rate (z h R B : PTm n) (hs : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] independentRate H H (headData (add z h) R B (initial R)) (headData z R B (initial R))
      (Hgain R zero (initial R)*norm1 h) B := by
  have hb := hs.andE₁
  have step : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h (norm1 h) := normSq_le_norm1_square h
  have dist : Γ ⊢[PRAAx] distanceBounded (ofGaussian (add z h) B) (ofGaussian z B) (norm1 h) B :=
    GaussianRationalReciprocal.bound_congr (point_increment z h B hb).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianBarnesCanonicalHeadPolynomialDerivative.step_bound h B (norm1 h) hb step)
  exact GaussianBarnesCanonicalHeadLipschitz.independent_rate (add z h) z R B B zero (initial R) (norm1 h) B hw hs hb dist

theorem rate (DP : PR 2) (z h R B d C A M : PTm n) (hs : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hh : Γ ⊢[PRAAx] le one (normSq h)) (hd : Γ ⊢[PRAAx] pointCN DP d)
    (hm : Γ ⊢[PRAAx] sampleBound DP d M)
    (hp : Γ ⊢[PRAAx] independentRate (QF P P) DP (qd P P (pd (add z h) B) (pd z B) h B) d (A*norm1 h) B)
    (hhead : Γ ⊢[PRAAx] independentRate (QF H H) DH
      (qd H H (headData (add z h) R B (initial R)) (headData z R B (initial R)) h B)
      (dhd z B (initial R)) (C*norm1 h) B) :
    Γ ⊢[PRAAx] independentRate (QF prefixF prefixF) (derivativeF DP)
      (qd prefixF prefixF (prefixData (add z h) R B) (prefixData z R B) h B)
      (derivativeData DP z R B d) ((gain R C A M*initial R)*norm1 h) (denominator R B) := by
  let z' := add z h
  let N := initial R
  let x := headData z R B N
  let x' := headData z' R B N
  let y := pd z B
  let y' := pd z' B
  let a := dhd z B N
  have hB := hs.andE₁
  have hN := initial_positive (Γ := Γ) R
  have hx := GaussianBarnesCanonicalHead.regular z R B zero N hs
  have hx' := GaussianBarnesCanonicalHead.regular z' R B zero N hw
  have hy := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) z B
  have hy' := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) z' B
  have joined := GaussianNamedNativeProductDerivativeRate.rate H P DH DP x' x y' y a d h B
    (A*norm1 h) (C*norm1 h) (Hgain R zero N*norm1 h) B M (Hcap R zero N) (Pcap R)
    hx' hx hy' hy (GaussianBarnesCanonicalHeadDerivativeJoin.regular z B N) hd (.andI hB hh) hB hm
    (head_samples_bound z' R B N hw) (prefactor_samples_bound z R B hs) hp hhead (head_rate z h R B hs hw)
  have swapped := GaussianNamedDifferenceQuotientProperness.proper prefixF (multiplyF H P) prefixF (multiplyF H P)
    (prefixData z' R B) (multiplyData H P x' y') (prefixData z R B) (multiplyData H P x y) h B
    (prefix_regular z' R B hw) (multiply_fast _ _ _ _ hx' hy') (prefix_regular z R B hs) (multiply_fast _ _ _ _ hx hy)
    (GaussianNameRingLaws.multiply_commutative P H y' x' hy' hx')
    (GaussianNameRingLaws.multiply_commutative P H y x hy hx)
  let F := QF prefixF prefixF
  let J := QF (multiplyF H P) (multiplyF H P)
  let I := derivativeF DP
  let r := qd (multiplyF H P) (multiplyF H P) (multiplyData H P x' y') (multiplyData H P x y) h B
  let t := qd prefixF prefixF (prefixData z' R B) (prefixData z R B) h B
  let w := derivativeData DP z R B d
  let K := norm1 h
  let U := Hcap R zero N
  let V := Hgain R zero N
  let W := Pcap R
  let S := U*(A*K)+M*(V*K)+W*(C*K)
  have toOrigin : Γ ⊢[PRAAx] independentRate F I t w S B :=
    GaussianNamedRateTransport.transport J I F I r w t w S B hB joined swapped (cross_refl _ _ (regular DP z R B d hs hd))
  refine GaussianNamedRateRadius.weaken F I t w S B ((gain R C A M*N)*K) (B*N) hB
    (positive_product _ _ hB hN) ?_ toOrigin
  apply le_of_eq_add (d := zero)
  change Γ ⊢[PRAAx] ((U*A+M*V+W*C)*N*K)*B ≐ (U*(A*K)+M*(V*K)+W*(C*K))*(B*N)+zero
  ipra_ring

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefixDerivativeJoin
