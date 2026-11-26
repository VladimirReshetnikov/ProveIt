import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderFirstPanelGridTerms
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderPanelRotation

/-!
# Exact first-order panel sum on the source harmonic grid

The panel is expressed using the literal original harmonic interval
and the literal inverse-square sum on the same mesh. This evaluates
the finite sampled panel before taking either named limit.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelSum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianStirlingAllOrderFirstPanelGridTerms (parts grid_parts gridIndex linearCoefficient squareCoefficient)
open GaussianStirlingAllOrderHarmonicIntegral (sum_at_original)
open GaussianStirlingAllOrderPanelRotation (nextBody next_term panel_right_endpoints)
open GaussianStirlingAllOrderPanelTail (panel panelBody panelData panel_row_at)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianStirlingAllOrderKernel (multiply_zero_right)
open GaussianRationalHorner (positive_product)
open RationalReciprocalPowerTail (tail tail_zero tail_succ reciprocalPower add_zero_right)
open RationalArithmetic (add multiply negative)
open RationalAlgebra (add_congr add_associative add_commutative multiply_congr multiply_add
  negative_congr negative_minus_multiply)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rsum" => RationalFiniteSum.sum

def result (U B Q L : PTm n) : PTm n :=
  add (negative (fraction L one))
    (add (multiply (fraction (linearCoefficient U B Q) one) (tail one (Q*U) L))
      (negative (multiply (fraction (squareCoefficient U B Q) one) (tail two (Q*U) L))))

@[simp] theorem subst_result {l : ℕ} (σ : Fin n → PTm l) (U B Q L : PTm n) :
    Syn.subst σ (result U B Q L) = result (Syn.subst σ U) (Syn.subst σ B) (Syn.subst σ Q) (Syn.subst σ L) :=
  by simp [result,linearCoefficient,squareCoefficient]

private theorem negative_add (a b : PTm n) : Γ ⊢[PRAAx] negative (add a b) ≐ add (negative a) (negative b) :=
  (negative_minus_multiply _).eqTrans ((multiply_add _ _ _).eqTrans
    (add_congr (negative_minus_multiply _).eqSymm (negative_minus_multiply _).eqSymm))

private theorem negative_zero : Γ ⊢[PRAAx] negative (fraction zero one : PTm n) ≐ fraction zero one :=
  (negative_minus_multiply _).eqTrans (multiply_zero_right _)

private theorem negative_successor (L : PTm n) : Γ ⊢[PRAAx]
    add (negative (fraction L one)) (negative (fraction one one)) ≐ negative (fraction (succ L) one) := by
  refine (negative_add _ _).eqSymm.eqTrans (negative_congr ?_)
  have hD : Γ ⊢[PRAAx] le one (one*one : PTm n) := by ipra_le 0
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (RationalRepresentations.represents_add _ _ _ _ _ _ (fraction_represents L one (le_refl one))
      (fraction_represents one one (le_refl one))) (fraction_represents _ _ (le_refl one)) hD (le_refl one)
  apply ZT.derive
  ipra_simps
  ring

private theorem interleave (a b c d : PTm n) : Γ ⊢[PRAAx]
    add (add a b) (add c d) ≐ add (add a c) (add b d) :=
  (add_associative a b _).eqTrans
    ((add_congr (.eqRefl a) ((add_associative b c d).eqSymm.eqTrans
      ((add_congr (add_commutative b c) (.eqRefl d)).eqTrans (add_associative c b d)))).eqTrans
      (add_associative a c _).eqSymm)

private theorem result_zero (U B Q : PTm n) : Γ ⊢[PRAAx] result U B Q zero ≐ fraction zero one := by
  let z : PTm n := fraction zero one
  have h : Γ ⊢[PRAAx] add z z ≐ z :=
    add_zero_right z (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
  have e (c e : PTm n) : Γ ⊢[PRAAx] multiply c (tail e (Q*U) zero) ≐ z :=
    (multiply_congr (.eqRefl _) (tail_zero e _)).eqTrans (multiply_zero_right _)
  exact (add_congr negative_zero (add_congr (e _ one) ((negative_congr (e _ two)).eqTrans negative_zero))).eqTrans
    ((add_congr (.eqRefl _) h).eqTrans h)

private theorem result_succ (U B Q L : PTm n) : Γ ⊢[PRAAx]
    add (result U B Q L) (parts U B Q (succ L)) ≐ result U B Q (succ L) := by
  let N := Q*U
  let p := fraction (linearCoefficient U B Q) one
  let q := fraction (squareCoefficient U B Q) one
  let D := succ (N+L)
  let a := multiply p (tail one N L)
  let b := negative (multiply q (tail two N L))
  let c := multiply p (reciprocalPower one (gridIndex U Q (succ L)))
  let d := negative (multiply q (reciprocalPower two (gridIndex U Q (succ L))))
  have ei : Γ ⊢[PRAAx] gridIndex U Q (succ L) ≐ D := by dsimp [gridIndex,D,N]; ipra_ring
  have e₁ : Γ ⊢[PRAAx] add a c ≐ multiply p (tail one N (succ L)) :=
    (add_congr (.eqRefl _) (multiply_congr (.eqRefl _) (RationalReciprocalPowerTail.reciprocal_congr (.eqRefl _) ei))).eqTrans
      ((multiply_add _ _ _).eqSymm.eqTrans (multiply_congr (.eqRefl _) (tail_succ one N L).eqSymm))
  have e₂ : Γ ⊢[PRAAx] add b d ≐ negative (multiply q (tail two N (succ L))) :=
    (add_congr (.eqRefl _) (negative_congr (multiply_congr (.eqRefl _)
      (RationalReciprocalPowerTail.reciprocal_congr (.eqRefl _) ei)))).eqTrans
      ((negative_add _ _).eqSymm.eqTrans (negative_congr ((multiply_add _ _ _).eqSymm.eqTrans
        (multiply_congr (.eqRefl _) (tail_succ two N L).eqSymm))))
  exact (interleave (negative (fraction L one)) (add a b) (negative (fraction one one)) (add c d)).eqTrans
    (add_congr (negative_successor L) ((interleave a b c d).eqTrans (add_congr e₁ e₂)))

def prefixLaw (A B Q k L : PTm n) : Fm PTm n :=
  le L (B*Q) ⟶ rsum (nextBody (panelBody 0)) L (panelData one A B (B*Q) k) ≐ result (A+B*k) B Q L

@[simp] theorem subst_prefixLaw {l : ℕ} (σ : Fin n → PTm l) (A B Q k L : PTm n) :
    (prefixLaw A B Q k L).subst σ = prefixLaw (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ Q) (Syn.subst σ k) (Syn.subst σ L) :=
  by simp [prefixLaw]

private theorem prefix_zero (A B Q k : PTm n) : Γ ⊢[PRAAx] prefixLaw A B Q k zero :=
  .impI ((RationalFiniteSum.sum_zero _ _).eqTrans
    (RationalReciprocalPowerTail.zero_fraction.eqSymm.eqTrans (result_zero (A+B*k) B Q).eqSymm))

private theorem prefix_succ (A B Q k L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le one Q)
    (ih : Γ ⊢[PRAAx] prefixLaw A B Q k L) : Γ ⊢[PRAAx] prefixLaw A B Q k (succ L) := by
  refine .impI ?_
  let Δ := le (succ L) (B*Q) :: Γ
  let d := panelData one A B (B*Q) k
  have right := RationalFiniteSum.sum_succ (Γ := Δ) (nextBody (panelBody 0)) L d
  rw [next_term] at right
  have e := (panel_row_at (Γ := Δ) 0 one A B (B*Q) k (succ L)).eqTrans
    (grid_parts A B Q k (succ L) hA.wk hB.wk hQ.wk Prf.hyp0)
  exact right.eqTrans ((add_congr (.impE ih.wk (le_trans (le_succ_self _) Prf.hyp0)) e).eqTrans
    (result_succ (A+B*k) B Q L))

theorem actual_prefix (A B Q k L : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] prefixLaw A B Q k L := by
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift A) (Syn.shift B) (Syn.shift Q) (Syn.shift k) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using prefix_zero (Γ := Γ) A B Q k
    · simp only [subst_prefixLaw,subst_repl_shift]
      have ha : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift A) := by simpa [Fm.shift,Syn.shift] using hA.shift
      have hb : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
      have hq : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift Q) := by simpa [Fm.shift,Syn.shift] using hQ.shift
      exact prefix_succ (Syn.shift A) (Syn.shift B) (Syn.shift Q) (Syn.shift k) (var 0) ha.wk hb.wk hq.wk Prf.hyp0
  simpa only [subst_prefixLaw,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using all.allE L

def panelValue (U B Q : PTm n) : PTm n :=
  multiply (fraction one (B*Q))
    (add (negative (fraction (B*Q) one))
      (add (multiply (fraction (linearCoefficient U B Q) one) (RationalHarmonicInterval.interval (U+B) U Q))
        (negative (multiply (fraction (squareCoefficient U B Q) one) (tail two (Q*U) (B*Q))))))

theorem actual_panel (A B Q k : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] panel 0 one A B (B*Q) k ≐ panelValue (A+B*k) B Q := by
  let U := A+B*k
  let M := B*Q
  have hM := positive_product _ _ hB hQ
  have first := panel_right_endpoints 0 one A B M k hM
  have second := Prf.impE (actual_prefix A B Q k M hA hB hQ) (le_refl M)
  have tailSwap : Γ ⊢[PRAAx] tail one (Q*U) M ≐ tail one (Q*U) (Q*B) := by
    simpa only [RationalReciprocalPowerTail.subst_tail,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (tail (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![one,Q*U,M]) (σ' := ![one,Q*U,Q*B]) (fun i => by
          fin_cases i
          exact .eqRefl _
          exact .eqRefl _
          exact mul_comm B Q)
  have e : Γ ⊢[PRAAx] tail one (Q*U) M ≐ RationalHarmonicInterval.interval (U+B) U Q :=
    tailSwap.eqTrans (sum_at_original U B Q)
  exact multiply_congr (.eqRefl _) (first.eqTrans (second.eqTrans
    (add_congr (.eqRefl _) (add_congr (multiply_congr (.eqRefl _) e) (.eqRefl _)))))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelSum
