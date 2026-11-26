import IPRADerivations.AnalyticNumberTheory.RobinLogName
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianEmbedding
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalFiniteSum
import IPRADerivations.Analysis.RationalArithmetic.Grids.RationalCubeMidpoint
import IPRADerivations.Core.CongruenceTactic

/-!
# Literal odd terms of the Robin logarithm

The actual lower numerator and denominator of the Robin enclosure
normalize to the original Gaussian rational sum of the odd terms
`2 a^(2j+1)/((2j+1)b^(2j+1))`. Every count, numerator and denominator
remains internal. The denominator certificates also apply at cutoff zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRobinOddLogarithm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz Lz Nz_zero Nz_succ Dz_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Pv P_succ L_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open GaussianRationalHorner
  (ofGaussian ofGaussian_represents qadd qzero represents positive_product represents_congr qadd_represents canonical_unique)
open GaussianRationalSyntheticDivision (qzero_canonical qadd_congr rescale_to)
open ComplexLogarithmRemainder (scale oneCode zeroCode)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_scale im_scale re_one im_one re_zero im_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def fraction (a b : PTm n) : PTm n := ofGaussian (scale a oneCode) b
def value (a b K : PTm n) : PTm n := fraction (Nz K a b) (Dz K a b)
def oddIndex (K : PTm n) : PTm n := succ (two*K)
def term (a b K : PTm n) : PTm n := fraction (two*Pv K a) (oddIndex K*Pv K b)
def body : PTm 2 := term (fstT (var 1)) (sndT (var 1)) (var 0)
def oddSum (a b K : PTm n) : PTm n := GaussianRationalFiniteSum.sum body K (pairT a b)

@[simp] theorem subst_fraction {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (fraction a b) = fraction (Syn.subst σ a) (Syn.subst σ b) := by simp [fraction]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (a b K : PTm n) :
    Syn.subst σ (value a b K) = value (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ K) := by simp [value]
@[simp] theorem subst_term {m : ℕ} (σ : Fin n → PTm m) (a b K : PTm n) :
    Syn.subst σ (term a b K) = term (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ K) := by
  simp [term,oddIndex]
@[simp] theorem subst_oddSum {m : ℕ} (σ : Fin n → PTm m) (a b K : PTm n) :
    Syn.subst σ (oddSum a b K) = oddSum (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ K) := by
  simp [oddSum]

theorem denominator_positive (a b K : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] le one (Dz K a b) :=
  le_congr (.eqRefl _) (Dz_pos (pos_of_one_le hb) K a).eqSymm (zero_lt_succ _)

theorem denominator_step (a b K : PTm n) : Γ ⊢[PRAAx]
    Dz (succ K) a b ≐ (oddIndex K*(b*b))*Dz K a b := by
  have e := natEq (congrMul (L_succ (Γ := Γ) K zero) (P_succ K b))
  apply deriveNat
  change Groth.ι (IPRA.Q.mk Γ (Lz (succ K) a b * Pv (succ K) b)) = _
  dsimp only [Lz,oddIndex,Dz] at e ⊢
  ipra_simps
  linear_combination e

theorem returned_term (a b K : PTm n) :
    Γ ⊢[PRAAx] inst2 body K (pairT a b) ≐ term a b K := by
  ipra_congr (term (var 0) (var 1) (var 2) : PTm 3) with [fst_pair _ _, snd_pair _ _, .eqRefl K] using [body, inst2]

theorem returned_sum_step (a b K : PTm n) : Γ ⊢[PRAAx]
    oddSum a b (succ K) ≐ qadd (oddSum a b K) (term a b K) :=
  (GaussianRationalFiniteSum.sum_succ body K (pairT a b)).eqTrans (qadd_congr (.eqRefl _) (returned_term a b K))

theorem value_zero (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] value a b zero ≐ qzero := by
  let D := Dz zero a b
  have hp := denominator_positive a b zero hb
  apply canonical_unique _ _ zeroCode D (GaussianRationalHorner.ofGaussian_canonical _ _ hp)
    qzero_canonical hp ?_ (GaussianRationalHorner.zero_represents D)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _)
    (ofGaussian_represents (scale (Nz zero a b) oneCode) D hp)
  have e := natEq (Nz_zero (Γ := Γ) a b)
  apply equal_of_values <;> simp only [re_scale,im_scale,re_one,im_one,re_zero,im_zero] <;>
    (try rw [e]) <;> ipra_simps <;> ring

theorem value_step (a b K : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] value a b (succ K) ≐ qadd (value a b K) (term a b K) := by
  let D := Dz (succ K) a b
  let d := Dz K a b
  let A := oddIndex K
  let S := b*b
  let l := Lz K a b
  let P := Pv K a
  let Q := Pv K b
  have hd := denominator_positive a b K hb
  have hD := denominator_positive a b (succ K) hb
  have hQ : Γ ⊢[PRAAx] le one Q := le_congr (.eqRefl _)
    (AnalyticNumberTheory.SigmaPrimePower.pos_pw (pos_of_one_le hb) (succ (two*K))).eqSymm (zero_lt_succ _)
  have hT : Γ ⊢[PRAAx] le one (A*Q) := positive_product _ _ (zero_lt_succ _) hQ
  have dstep : Γ ⊢[PRAAx] d*(A*S) ≐ D := (mul_comm _ _).eqTrans (denominator_step a b K).eqSymm
  have tstep : Γ ⊢[PRAAx] (A*Q)*(l*S) ≐ D := by
    exact (show Γ ⊢[PRAAx] (A*Q)*(l*S) ≐ (A*S)*d by dsimp only [d,Dz]; ipra_ring).eqTrans
      (denominator_step a b K).eqSymm
  have x := rescale_to (value a b K) (scale (Nz K a b) oneCode) d (A*S) D
    (ofGaussian_represents _ _ hd) dstep
  have y := rescale_to (term a b K) (scale (two*P) oneCode) (A*Q) (l*S) D
    (ofGaussian_represents _ _ hT) tstep
  have sumVal := qadd_represents _ _ _ _ _ hD x y
  apply canonical_unique _ _ _ D (GaussianRationalHorner.ofGaussian_canonical _ _ hD)
    (GaussianRationalHorner.qadd_canonical _ _) hD ?_ sumVal
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents (scale (Nz (succ K) a b) oneCode) D hD)
  have e := natEq (Nz_succ (Γ := Γ) K a b)
  apply equal_of_values <;> simp only [re_scale,im_scale,re_add,im_add,re_one,im_one,A,S,l,P,oddIndex] <;>
    (try rw [e]) <;> (try ipra_simps) <;> ring

def sumLaw (a b K : PTm n) : Fm PTm n := value a b K ≐ oddSum a b K
@[simp] theorem subst_sumLaw {m : ℕ} (σ : Fin n → PTm m) (a b K : PTm n) :
    (sumLaw a b K).subst σ = sumLaw (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ K) := by simp [sumLaw]

theorem literal_value (a b K : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] value a b K ≐ oddSum a b K := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift b) := by
    simpa [Fm.shift,Syn.shift] using hb.shift
  have aLL : Γ ⊢[PRAAx] .all (sumLaw (Syn.shift a) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (value_zero a b hb).eqTrans (GaussianRationalFiniteSum.sum_zero body (pairT a b)).eqSymm
    · simp only [subst_sumLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (value_step _ _ _ hs.wk).eqTrans
        ((qadd_congr Prf.hyp0 (.eqRefl _)).eqTrans (returned_sum_step _ _ _).eqSymm)
  change Γ ⊢[PRAAx] sumLaw a b K
  simpa only [subst_sumLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using aLL.allE K

theorem embedded_value (a b K : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] RationalGaussianEmbedding.embed (RationalCubeMidpoint.fraction (Nz K a b) (Dz K a b))
      ≐ oddSum a b K := by
  let P := Nz K a b
  let D := Dz K a b
  have hp := denominator_positive a b K hb
  have embed := RationalGaussianEmbedding.embed_from_representation (RationalCubeMidpoint.fraction P D) (ZT.ofNat P) D
    (RationalIntegerNormalization.normalize_preserves_value (ZT.ofNat P) D hp)
  have eq : Γ ⊢[PRAAx] equal (RationalGaussianEmbedding.native (ZT.ofNat P)) (scale P oneCode) := by
    apply equal_of_values <;>
      simp only [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,
        ComplexLogarithmRemainder.eval_im_code,re_scale,im_scale,re_one,im_one,ZT.toZ_ofNat] <;>
      (try ipra_simps) <;> ring
  have canonical := canonical_unique _ _ _ D (RationalGaussianEmbedding.embed_canonical _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hp) hp
    (represents_congr (.eqRefl _) eq (.eqRefl _) embed)
    (ofGaussian_represents (scale P oneCode) D hp)
  exact canonical.eqTrans (literal_value a b K hb)

theorem original_Robin_odd_series_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ RationalGaussianEmbedding.embed
      (RationalCubeMidpoint.fraction (Nz (var 2) (var 0) (var 1)) (Dz (var 2) (var 0) (var 1)))
        ≐ oddSum (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (embedded_value _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRobinOddLogarithm
