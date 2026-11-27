import IPRADerivations.Analysis.Stirling.Expansions.OddSeries.GaussianStirlingOddCoefficients
import IPRADerivations.Analysis.Stirling.Expansions.OddSeries.GaussianStirlingOddLogBrackets

/-!
# Reading the exact scalar Robin bounds as the Stirling bounds

The affine operation ((2A+B)/(2B)\,L-1) cancels the first odd
logarithm term. It sends the upper endpoint to the same finite sum
plus the specified sharp tail.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingOddReadback

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Pv Lv)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Dz Un Ud Lz L_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open GaussianStirlingDifference (coefficient minusOne)
open GaussianStirlingOddSeries (partialSum partial_zero partial_succ tail baseDenominator degree)
open GaussianStirlingOddLogBrackets (logLower logUpper gap_positive upper_denominator_positive)
open GaussianStirlingOddGrid (gap denominator_positive)
open GaussianStirlingOddCoefficients
  (fraction_equal fraction_add_same fraction_embed first_term scaled_term scaled_odd_fraction additive_constant_zero base_positive)
open GaussianRationalHorner (qzero qadd qmul positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qzero_add)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalLinearProduct (qadd_commutative)
open GaussianPositiveRationalLogarithm (fraction)
open RationalGaussianEmbedding (embed)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def affine (A B q : PTm n) : PTm n := qadd (qmul (coefficient A B) q) minusOne

ipra_subst affine [minusOne, GaussianRationalMatrixFiniteSums.minusOne]

theorem affine_congr (A B : PTm n) {q r : PTm n} (e : Γ ⊢[PRAAx] q ≐ r) :
    Γ ⊢[PRAAx] affine A B q ≐ affine A B r :=
  qadd_congr (qmul_congr (.eqRefl _) e) (.eqRefl _)

private theorem affine_split (A B u v : PTm n) : Γ ⊢[PRAAx]
    affine A B (qadd u v) ≐ qadd (affine A B u) (qmul (coefficient A B) v) := by
  let c := coefficient A B
  let p := qmul c u
  let q := qmul c v
  exact (qadd_congr (GaussianRationalCoefficientScaling.qmul_add c u v) (.eqRefl _)).eqTrans
    ((qadd_associative p q minusOne).eqTrans
      ((qadd_congr (.eqRefl _) (qadd_commutative q minusOne)).eqTrans (qadd_associative p minusOne q).eqSymm))

private def valueLaw (A B K : PTm n) : Fm PTm n :=
  affine A B (GaussianRobinOddLogarithm.value B (baseDenominator A B) (succ K)) ≐ partialSum A B K

@[simp] private theorem subst_valueLaw {l : ℕ} (σ : Fin n → PTm l) (A B K : PTm n) :
    (valueLaw A B K).subst σ = valueLaw (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ K) := by
  simp [valueLaw]

private theorem finite_zero (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] valueLaw A B zero := by
  let s := baseDenominator A B
  let t := GaussianRobinOddLogarithm.term B s zero
  have hs := base_positive A B hA
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical t := GaussianRationalHorner.ofGaussian_canonical _ _
    (positive_product _ _ (zero_lt_succ (two*zero)) (GaussianFactorBudget.power_positive s (succ (two*zero)) hs))
  have e := (GaussianRobinOddLogarithm.value_step B s zero hs).eqTrans
    ((qadd_congr (GaussianRobinOddLogarithm.value_zero B s hs) (.eqRefl _)).eqTrans (qzero_add t hc))
  exact (affine_congr A B e).eqTrans ((qadd_congr (first_term A B hA hB) (.eqRefl _)).eqTrans
    (additive_constant_zero.eqTrans (partial_zero A B).eqSymm))

private theorem finite_step (A B K : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (ih : Γ ⊢[PRAAx] valueLaw A B K) : Γ ⊢[PRAAx] valueLaw A B (succ K) := by
  let s := baseDenominator A B
  let u := GaussianRobinOddLogarithm.value B s (succ K)
  let v := GaussianRobinOddLogarithm.term B s (succ K)
  exact (affine_congr A B (GaussianRobinOddLogarithm.value_step B s (succ K) (base_positive A B hA))).eqTrans
    ((affine_split A B u v).eqTrans ((qadd_congr ih (scaled_term A B K hA hB)).eqTrans (partial_succ A B K).eqSymm))

private theorem finite_value (A B K : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] valueLaw A B K := by
  let sh (q : PTm n) := Syn.shift q
  have a : Γ.map Fm.shift ⊢[PRAAx] le one (sh A) := by simpa [Fm.shift,Syn.shift,sh] using hA.shift
  have b : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh] using hB.shift
  have hall : Γ ⊢[PRAAx] .all (valueLaw (sh A) (sh B) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_valueLaw,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using finite_zero A B hA hB
    · simpa only [subst_valueLaw,sh,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        finite_step (sh A) (sh B) (var 0) a.wk b.wk Prf.hyp0
  simpa only [subst_valueLaw,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE K

theorem lower_readback (A B K : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] affine A B (embed (logLower A B (succ K))) ≐ partialSum A B K := by
  have eq := fraction_embed (GaussianStirlingOddGrid.numerator A (succ K) B)
    (GaussianStirlingOddGrid.denominator A (succ K) B) (denominator_positive A (succ K) B hA)
  exact (affine_congr A B eq).eqTrans (finite_value A B K hA hB)

private theorem expand_upper (A B K : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] embed (logUpper A B (succ K)) ≐
      qadd (embed (logLower A B (succ K)))
        (fraction (two*Pv (succ K) B*(baseDenominator A B*baseDenominator A B))
          (succ (degree K)*gap A B*Pv (succ K) (baseDenominator A B))) := by
  let k := succ K
  let s := baseDenominator A B
  let P := Pv k s
  let L := Lv k zero
  let N := Nz k B s
  let D := Dz k B s
  let H := two*Pv k B*(s*s)
  let T := succ (degree K)*gap A B
  have ds := denominator_positive A k B hA
  have du := upper_denominator_positive A B k hA
  have hs := base_positive A B hA
  have w := gap_positive A B hA
  have p := GaussianFactorBudget.power_positive s (succ (degree K)) hs
  have dC := positive_product _ _ (positive_product _ _ (zero_lt_succ (degree K)) w) p
  have lower := fraction_embed N D ds
  have top := fraction_embed (Un k B s (gap A B)) (Ud k B s (gap A B)) du
  have l : Γ ⊢[PRAAx] fraction N D ≐ fraction (N*T) (T*D) :=
    fraction_equal _ _ _ _ ds du (by ipra_ring)
  have r : Γ ⊢[PRAAx] fraction H (T*P) ≐ fraction (H*L) (T*D) := by
    apply fraction_equal _ _ _ _ dC du
    change Γ ⊢[PRAAx] H*(T*(L*P)) ≐ (H*L)*(T*P)
    ipra_ring
  have e : Γ ⊢[PRAAx] fraction (N*T+H*L) (T*D) ≐ fraction (Un k B s (gap A B)) (Ud k B s (gap A B)) := by
    apply fraction_equal _ _ _ _ du du
    have d : Γ ⊢[PRAAx] N*T+H*L ≐ Un k B s (gap A B) := by
      change Γ ⊢[PRAAx] N*T+H*L ≐ N*succ (two*k)*gap A B+H*L
      dsimp only [T,degree,k]
      ipra_ring
    exact congrMul d (.eqRefl _)
  exact top.eqTrans ((qadd_congr (lower.eqTrans l) r).eqTrans
    ((fraction_add_same (N*T) (H*L) (T*D) du).eqTrans e)).eqSymm

theorem upper_readback (A B K : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] affine A B (embed (logUpper A B (succ K))) ≐ qadd (partialSum A B K) (tail A B K) := by
  let s := baseDenominator A B
  let C := fraction (two*Pv (succ K) B*(s*s)) (succ (degree K)*gap A B*Pv (succ K) s)
  exact (affine_congr A B (expand_upper A B K hA)).eqTrans ((affine_split A B (embed (logLower A B (succ K))) C).eqTrans
    (qadd_congr (lower_readback A B K hA hB) (scaled_odd_fraction A B K (s*s) (gap A B) hA hB (gap_positive A B hA))))

end LeanProofs.IPRA.Analysis.GaussianStirlingOddReadback
