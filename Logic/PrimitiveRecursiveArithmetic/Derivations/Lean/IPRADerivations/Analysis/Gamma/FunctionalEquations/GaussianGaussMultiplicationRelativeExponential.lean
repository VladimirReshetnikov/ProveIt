import IPRADerivations.Analysis.Exponential.GaussianExponentialUnitPerturbation
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGaussMultiplicationPowerRate
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGaussMultiplicationRelativeLog

/-!
# The sharp relative exponential for the Gauss multiplication powers

The harmonic logarithm correction has an exact sample bound. After
multiplying by (mz-1), the actual radius-one exponential is within
(2m(R+1)/N) of one at every clock when (Nge m(R+1)).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationRelativeExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGaussMultiplicationPowerRate
  (amplification multiplier multiplier_bound exponentF exponentData rowLogData limitLogData)
open GaussianGaussMultiplicationRelativeLog
  (relativeLogF relativeLogData relative_log_bound_at relative_log_regular relative_log_addition)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_to_diagonal cross_symm cross_trans)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSyntheticDivision (qone)
open GaussianRadiusExponentialName (input nameF data sample index query)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def relativeF : PR 2 := GaussianBoundedConstantProductName.nameF relativeLogF
def relativeData (z R B m N : PTm n) : PTm n :=
  GaussianBoundedConstantProductName.data (amplification R m) (multiplier z B m) (relativeLogData m N)
def relativeExpF : PR 2 := nameF relativeF
def relativeExpData (z R B m N : PTm n) : PTm n := data one (relativeData z R B m N)

@[simp] theorem subst_relativeData {l : ℕ} (σ : Fin n → PTm l) (z R B m N : PTm n) :
    Syn.subst σ (relativeData z R B m N) =
      relativeData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ N) := by
  simp [relativeData]
@[simp] theorem subst_relativeExpData {l : ℕ} (σ : Fin n → PTm l) (z R B m N : PTm n) :
    Syn.subst σ (relativeExpData z R B m N) =
      relativeExpData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ N) := by
  simp [relativeExpData]

theorem relative_sample_bound (z R B m N p : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N)
    (hc : Γ ⊢[PRAAx] bounded (multiplier z B m) (amplification R m) one) : Γ ⊢[PRAAx]
    bounded (ap2 relativeF p (relativeData z R B m N)) (amplification R m) N := by
  let A := amplification R m
  let c := multiplier z B m
  let x := relativeLogData m N
  have primary := GaussianRationalReciprocal.bounded_product c _ A one one N
    (le_refl one) hN hc (relative_log_bound_at m N (GaussianBoundedConstantProductName.clock p A) hm hN)
  exact GaussianRationalReciprocal.bound_congr
    (GaussianBoundedConstantProductName.sample_at relativeLogF p A c x).eqSymm
    (by ipra_ring) (one_mul _) primary

theorem relative_regular (z R B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N)
    (hc : Γ ⊢[PRAAx] bounded (multiplier z B m) (amplification R m) one) : Γ ⊢[PRAAx]
    pointCN relativeF (relativeData z R B m N) :=
  GaussianBoundedConstantProductName.name_regular relativeLogF _ _ _ (.andI (relative_log_regular m N hm hN) hc)

theorem relative_sample_canonical (z R B m N p : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 relativeF p (relativeData z R B m N)) :=
  GaussianRationalHorner.canonical_congr
    (GaussianBoundedConstantProductName.sample_at relativeLogF p (amplification R m) (multiplier z B m) (relativeLogData m N))
    (GaussianRationalHorner.qmul_canonical _ _)

theorem relative_input (z R B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le (amplification R m) N)
    (hc : Γ ⊢[PRAAx] bounded (multiplier z B m) (amplification R m) one) : Γ ⊢[PRAAx]
    input relativeF one (relativeData z R B m N) := by
  refine .andI (relative_regular z R B m N hm hN hc) (.allI ?_)
  let sh (x : PTm n) := Syn.shift x
  have ms : Γ.map Fm.shift ⊢[PRAAx] le one (sh m) := by simpa [Fm.shift,Syn.shift,sh] using hm.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh] using hN.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] bounded (multiplier (sh z) (sh B) (sh m)) (amplification (sh R) (sh m)) one := by
    simpa [Fm.shift,Syn.shift,sh] using hc.shift
  have ast : Γ.map Fm.shift ⊢[PRAAx] le (amplification (sh R) (sh m)) (sh N) := by
    simpa [Fm.shift,Syn.shift,sh] using hA.shift
  have v := relative_sample_bound (sh z) (sh R) (sh B) (sh m) (sh N) (var 0) ms ns cs
  simpa [Syn.shift,sh] using GaussianExponentialSmallPerturbation.unit_disk_of_small_bound _ _ _ ns ast v

theorem relative_exponential_near_one (z R B m N p : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le (amplification R m) N)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 relativeExpF p (relativeExpData z R B m N)) qone (two*amplification R m) N := by
  let x := relativeData z R B m N
  let t := GaussianRadiusExponentialName.inputPrecision one p
  let K := index one p
  have small := relative_sample_bound z R B m N t hm hN (multiplier_bound z R B m hm hB hz)
  have extra : Γ ⊢[PRAAx] le two (GaussianRationalExponentialTail.cutoff one (p+num 4)) := by
    unfold GaussianRationalExponentialTail.cutoff ExponentialTail.Nt
    ipra_le 𝔞 p+10
  have hK : Γ ⊢[PRAAx] le one K := (succ_monus_succ one K).eqSymm.eqTrans
    (le_congr (.eqRefl _) (GaussianRationalExponentialTail.last_successor one (p+num 4)).eqSymm extra)
  exact GaussianRationalDistanceOrder.distance_congr
    (GaussianRadiusExponentialName.sample_at relativeF one p x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianExponentialUnitPerturbation.finite_two _ _ _ K hN hA small (relative_sample_canonical z R B m N t) hK)

theorem exponent_addition (z R B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    crossEquivalent exponentF (addF exponentF relativeF) (exponentData z R B m (rowLogData m N))
      (addData (exponentData z R B m (limitLogData m)) (relativeData z R B m N)) := by
  let A := amplification R m
  let c := multiplier z B m
  let x := rowLogData m N
  let y := limitLogData m
  let w := relativeLogData m N
  let g := addF logF relativeLogF
  have hc := multiplier_bound z R B m hm hB hz
  have hx := GaussianGaussMultiplicationPowerRate.row_log_regular m N hm hN
  have hy := GaussianGaussMultiplicationPowerRate.limit_log_regular m hm
  have hw := relative_log_regular m N hm hN
  have hcf := constant_regular (Γ := Γ) c
  have hx' := GaussianBoundedConstantProductName.ordinary_product_identity logF A c x (.andI hx hc)
  have hy' := GaussianBoundedConstantProductName.ordinary_product_identity logF A c y (.andI hy hc)
  have hw' := GaussianBoundedConstantProductName.ordinary_product_identity relativeLogF A c w (.andI hw hc)
  have trans := GaussianNameArithmetic.multiply_equivalent constantF constantF logF g c c x (addData y w)
    hcf hcf hx (GaussianNameArithmetic.add_fast logF relativeLogF y w hy hw)
    (cross_to_diagonal _ _ _ _ (cross_refl constantF c hcf))
    (cross_to_diagonal _ _ _ _ (relative_log_addition m N hm hN))
  have dist := GaussianNameRingLaws.distributive constantF logF relativeLogF c y w hcf hy hw
  have hyR := GaussianNameArithmetic.multiply_fast constantF logF c y hcf hy
  have hwR := GaussianNameArithmetic.multiply_fast constantF relativeLogF c w hcf hw
  have hyB := GaussianBoundedConstantProductName.name_regular logF A c y (.andI hy hc)
  have hwB := relative_regular z R B m N hm hN hc
  have add := GaussianNamedGammaHalfShift.add_cross (multiplyF constantF logF) exponentF
    (multiplyF constantF relativeLogF) relativeF (multiplyData constantF logF c y) (exponentData z R B m y)
    (multiplyData constantF relativeLogF c w) (relativeData z R B m N) hyR hyB hwR hwB
    (cross_symm _ _ _ _ hy') (cross_symm _ _ _ _ hw')
  exact cross_trans _ _ _ _ _ _ (cross_trans _ _ _ _ _ _ (cross_trans _ _ _ _ _ _ hx' trans) dist) add

theorem actual_gauss_multiplication_relative_exponential_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 3) ⋏ (le one (var 4) ⋏ (le (amplification (var 1) (var 3)) (var 4) ⋏
      (le one (var 2) ⋏ ComplexLogarithmRemainder.bounded (var 0) (var 1*var 2))))) ⟶
      distanceBounded (ap2 relativeExpF (var 5) (relativeExpData (var 0) (var 1) (var 2) (var 3) (var 4)))
        qone (two*amplification (var 1) (var 3)) (var 4)) :=
  closeUniv 6 (.impI (relative_exponential_near_one _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationRelativeExponential
