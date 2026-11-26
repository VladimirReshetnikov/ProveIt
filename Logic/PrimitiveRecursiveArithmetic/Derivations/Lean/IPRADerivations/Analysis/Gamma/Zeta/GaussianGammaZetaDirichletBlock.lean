import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaDirichletRowDecay
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteSumFamilyRange
import IPRADerivations.Analysis.Inequalities.GaussianRationalFactorialEulerSums

/-!
# Finite Dirichlet mass inside one dyadic block

The actual prefix observations at a common row clock differ by the
literal sum of the intervening rows. On every subinterval of
[(2^h)^A,(2^(h+1))^A], this contributes at most 2^A/2^h plus
3/2^p per retained row.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletBlock

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerPositiveScalingConstant (inverseF inverseData)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaZetaDirichletRowDecay (block block_positive row_decay)
open GaussianGammaZetaMellinDampedImproper (dirichletBody parameters dirichlet_at)
open GaussianNamedFiniteSumFamily (body finite term_at)
open GaussianNamedFiniteSumFamilyRange (rangeBody range_row_at finite_split)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalRiemannRefinement (constantBody constant_entry constant_sum termsDistance sum_distance)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianEulerIntegralGammaIdentification.source
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def value (p N z R B A : PTm n) : PTm n :=
  finite inverseF dirichletBody p N (parameters (shifted z B) (R+one) B A)

@[simp] theorem subst_prefix {m : ℕ} (σ : Fin n → PTm m) (p N z R B A : PTm n) :
    Syn.subst σ (value p N z R B A) =
      value (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by
  simp [value,GaussianNamedFiniteSumFamily.finite,one]

theorem block_succ (A h : PTm n) : Γ ⊢[PRAAx] block A (succ h) ≐ block A h*unit A := by
  unfold block
  exact (congrAp2 powF (.eqRefl A) (GaussianRationalHalfAngleRecovery.unit_succ h)).eqTrans
    ((AnalyticNumberTheory.LocalFactor.pw_mul_base _ _ _).eqTrans (mul_comm _ _))

private theorem row_at (p j N z R B A : PTm n) :
    Γ ⊢[PRAAx] inst2 (body inverseF (rangeBody dirichletBody)) j
      (pairT p (pairT N (parameters (shifted z B) (R+one) B A))) ≐
      ap2 inverseF p (inverseData (shifted z B) B (succ (N+j)) one) := by
  let x := parameters (shifted z B) (R+one) B A
  exact (term_at inverseF (rangeBody dirichletBody) j p (pairT N x)).eqTrans
    (congrAp2 inverseF (.eqRefl p) ((range_row_at dirichletBody N j x).eqTrans
      (dirichlet_at (N+j) (shifted z B) (R+one) B A)))

private theorem row_majorant (p z R B A h i : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hi : Γ ⊢[PRAAx] le (block A h) i) :
    Γ ⊢[PRAAx] bounded (ap2 inverseF p (inverseData (shifted z B) B i one))
      (unit p+num 3*(block A h*unit h)) (block A h*unit h*unit p) := by
  let J := block A h
  let H := unit h
  let U := unit p
  have hH := unit_positive (Γ := Γ) h
  have hU := unit_positive (Γ := Γ) p
  have hJ := block_positive (Γ := Γ) A h
  exact bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (le_trans hJ hi) hH) hU)
    (positive_product _ _ (positive_product _ _ hJ hH) hU)
    (by change Γ ⊢[PRAAx] le ((U+num 3*(i*H))*(J*H*U)) ((U+num 3*(J*H))*(i*H*U))
        ipra_le 𝔞(H*U*U)*sl hi)
    (row_decay p z R B A h i hz hi)

theorem block_error (p N r z R B A h : PTm n) (hz : Γ ⊢[PRAAx] S z R B A)
    (hN : Γ ⊢[PRAAx] le (block A h) N) (hr : Γ ⊢[PRAAx] le r (block A h*unit A)) :
    Γ ⊢[PRAAx] distanceBounded (value p (N+r) z R B A) (value p N z R B A)
      (unit A*unit p+num 3*r*unit h) (unit h*unit p) := by
  let J := block A h
  let H := unit h
  let U := unit p
  let C := unit A
  let c := U+num 3*(J*H)
  let d := J*H*U
  let x := parameters (shifted z B) (R+one) B A
  let y := pairT p (pairT N x)
  let t := body inverseF (rangeBody dirichletBody)
  have hJ := block_positive (Γ := Γ) A h
  have hH := unit_positive (Γ := Γ) h
  have hU := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ (positive_product _ _ hJ hH) hU
  have rows : Γ ⊢[PRAAx] termsDistance t constantBody r y qzero c d := by
    refine .allI (.impI ?_)
    let sh (v : PTm n) := Syn.shift v
    let j : PTm (n+1) := var 0
    let Δ := lt j (sh r)::Γ.map Fm.shift
    have margin : Δ ⊢[PRAAx] le (block (sh A) (sh h)) (sh N) :=
      by simpa [Fm.shift,sh,Δ,Syn.shift] using hN.shift.wk
    have source : Δ ⊢[PRAAx] S (sh z) (sh R) (sh B) (sh A) :=
      by simpa [Fm.shift,sh,Δ,Syn.shift] using hz.shift.wk
    have hit := le_trans margin (le_trans (le_add_right (sh N) j) (le_succ_self (sh N+j)))
    have b := row_majorant (sh p) (sh z) (sh R) (sh B) (sh A) (sh h) (succ (sh N+j)) source hit
    let w := ap2 inverseF (sh p) (inverseData (shifted (sh z) (sh B)) (sh B) (succ (sh N+j)) one)
    have canon : Δ ⊢[PRAAx] GaussianRationalHorner.canonical w :=
      GaussianRadiusExponentialName.sample_canonical
        (GaussianNameRingLaws.negativeF GaussianEulerPositiveScalingConstant.exponentF)
        (GaussianEulerPositiveScalingConstant.radius (shifted (sh z) (sh B)) (sh B) (succ (sh N+j)) one)
        (sh p) (GaussianNameRingLaws.negativeData
          (GaussianEulerPositiveScalingConstant.exponentData (shifted (sh z) (sh B)) (sh B) (succ (sh N+j)) one))
    have near : Δ ⊢[PRAAx] distanceBounded w qzero _
        (block (sh A) (sh h)*unit (sh h)*unit (sh p)) :=
      bound_congr (GaussianRationalReconstruction.qsub_zero_right w canon).eqSymm (.eqRefl _) (.eqRefl _) b
    have e := row_at (Γ := Δ) (sh p) j (sh N) (sh z) (sh R) (sh B) (sh A)
    simpa only [Δ,t,y,x,sh,j,J,H,U,c,d,Syn.shift,subst_pairT,
      GaussianGammaZetaMellinDampedImproper.subst_parameters,GaussianGammaEulerHeadShift.subst_shifted,
      PTm.subst_add,PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit,GaussianGammaZetaDirichletRowDecay.subst_block,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,PTm.subst_num,
      GaussianRationalHorner.subst_qzero,constant_entry] using
      distance_congr e.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) near
  have summed := sum_distance t constantBody r y qzero c d hd rows
  have z0 := (constant_sum (Γ := Γ) qzero r).eqTrans (GaussianRationalFactorialEulerSums.scale_zero_value r)
  let interval := finite inverseF (rangeBody dirichletBody) p r (pairT N x)
  have bound : Γ ⊢[PRAAx] bounded interval (r*c) d :=
    bound_congr (GaussianRationalReconstruction.qsub_zero_right interval
      (GaussianRationalFiniteSum.sum_canonical t r y)) (.eqRefl _) (.eqRefl _)
      (distance_congr (.eqRefl _) z0 (.eqRefl _) (.eqRefl _) summed)
  have split := finite_split (Γ := Γ) inverseF dirichletBody p N r x
  have read : Γ ⊢[PRAAx] qsub (value p (N+r) z R B A) (value p N z R B A) ≐ interval :=
    (GaussianRationalSyntheticDivision.qsub_congr split (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel (value p N z R B A) interval
        (GaussianRationalFiniteSum.sum_canonical t r y))
  apply distance_radius_mono _ _ _ _ _ _ hd (positive_product _ _ hH hU)
    _ (bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) bound)
  change Γ ⊢[PRAAx] le ((r*c)*(H*U)) ((C*U+num 3*r*H)*d)
  unfold c d
  ipra_le 𝔞(H*U*U)*sl hr

end LeanProofs.IPRA.Analysis.GaussianGammaZetaDirichletBlock
