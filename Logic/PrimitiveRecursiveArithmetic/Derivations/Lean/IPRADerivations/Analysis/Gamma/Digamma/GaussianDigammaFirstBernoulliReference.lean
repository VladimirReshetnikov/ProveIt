import IPRADerivations.Analysis.Gamma.Digamma.GaussianDigammaFirstBernoulliLocal
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaHarmonicPrefix
import IPRADerivations.Analysis.LinearAlgebra.GaussianDeterminantSignTransport

/-!
# Exact local decomposition for the digamma reference telescope

A trapezoid minus its harmonic cell is the left reciprocal plus
the forward difference of the half-reciprocal minus the harmonic prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliReference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianDigammaFirstBernoulliEndpoints (trapezoid)
open GaussianDigammaFirstBernoulliLocal (reference embed_sub)
open GaussianGammaDigammaFiniteSum (index row_source)
open GaussianGammaDigammaHarmonicCells (cell chain halfReciprocal half_pair cell_zero)
open GaussianGammaDigammaHarmonicPrefix (index_succ)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (canonical ofGaussian_canonical qadd qzero positive_product)
open GaussianRationalMetric (qsub qnegative)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qadd_sub_cancel)
open GaussianReciprocalHorner (qadd_commutative)
open GaussianStirlingGammaLogarithm (source)
open RationalGaussianEmbedding (embed embed_add embed_canonical)
open RationalGaussianRealPart (embed_congr)
open RationalHarmonicInterval (interval at_common common horizon)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def harmonicPrefix (A B Q k : PTm n) : PTm n := embed (interval (index A B k) A Q)

def anchor (A B Q k : PTm n) : PTm n :=
  qsub (halfReciprocal (index A B k) B) (harmonicPrefix A B Q k)

@[simp] theorem subst_harmonicPrefix {l : ℕ} (σ : Fin n → PTm l) (A B Q k : PTm n) :
    Syn.subst σ (harmonicPrefix A B Q k) = harmonicPrefix (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ Q) (Syn.subst σ k) :=
  by simp [harmonicPrefix]

@[simp] theorem subst_anchor {l : ℕ} (σ : Fin n → PTm l) (A B Q k : PTm n) :
    Syn.subst σ (anchor A B Q k) = anchor (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ Q) (Syn.subst σ k) :=
  by simp [anchor]

@[simp] theorem subst_reference {l : ℕ} (σ : Fin n → PTm l) (U B Q : PTm n) :
    Syn.subst σ (reference U B Q) = reference (Syn.subst σ U) (Syn.subst σ B) (Syn.subst σ Q) :=
  by simp [reference,trapezoid,two]

theorem interval_congr {a b a' b' Q : PTm n} (hA : Γ ⊢[PRAAx] a ≐ a') (hB : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] interval a b Q ≐ interval a' b' Q := by
  simpa only [RationalHarmonicInterval.subst_interval,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (interval (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![a,b,Q]) (σ' := ![a',b',Q]) (fun i => by fin_cases i <;> first | exact hA | exact hB | exact .eqRefl _)

theorem half_congr {a a' b : PTm n} (h : Γ ⊢[PRAAx] a ≐ a') :
    Γ ⊢[PRAAx] halfReciprocal a b ≐ halfReciprocal a' b :=
  GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (congrMul (.eqRefl _) h)

theorem harmonic_difference (A u v Q : PTm n) :
    Γ ⊢[PRAAx] qsub (embed (interval v A Q)) (embed (interval u A Q)) ≐ embed (interval v u Q) := by
  let L := Q*(A+u+v)
  let X := cell v A Q L
  let Y := cell u A Q L
  let Z := cell v u Q L
  have hv : Γ ⊢[PRAAx] le (horizon v A Q) L := le_of_eq_add (d := Q*u) (by unfold horizon L; ipra_ring)
  have hu : Γ ⊢[PRAAx] le (horizon u A Q) L := le_of_eq_add (d := Q*v) (by unfold horizon L; ipra_ring)
  have h₁ : Γ ⊢[PRAAx] le (horizon v u Q) L := le_of_eq_add (d := Q*A) (by unfold horizon L; ipra_ring)
  have eX : Γ ⊢[PRAAx] X ≐ embed (interval v A Q) := embed_congr (at_common v A Q L hv)
  have eY : Γ ⊢[PRAAx] Y ≐ embed (interval u A Q) := embed_congr (at_common u A Q L hu)
  have eZ : Γ ⊢[PRAAx] Z ≐ embed (interval v u Q) := embed_congr (at_common v u Q L h₁)
  have join : Γ ⊢[PRAAx] qadd Y Z ≐ X := chain A u v Q L
  exact (qsub_congr (eX.eqSymm.eqTrans join.eqSymm) eY.eqSymm).eqTrans
    ((qadd_sub_cancel Y Z (embed_canonical _)).eqTrans eZ)

private theorem nested_difference (x y u v : PTm n) (hv : Γ ⊢[PRAAx] canonical v) :
    Γ ⊢[PRAAx] qsub (qsub x u) (qsub y v) ≐ qsub (qsub x y) (qsub u v) := by
  have swap : Γ ⊢[PRAAx] qsub (qnegative u) (qnegative v) ≐ qsub v u :=
    (qadd_congr (.eqRefl _) (GaussianDeterminantSignTransport.negative_involution v hv)).eqTrans (qadd_commutative _ _)
  exact (GaussianNameArithmetic.sum_difference x y (qnegative u) (qnegative v)).eqTrans
    (qadd_congr (.eqRefl _) (swap.eqTrans (GaussianRationalDistanceOrder.reversed_difference u v).eqSymm))

theorem reference_row (A B Q k : PTm n) (hs : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] embed (reference (index A B k) B Q) ≐
      qadd (fraction B (index A B k)) (qsub (anchor A B Q (succ k)) (anchor A B Q k)) := by
  let U := index A B k
  let V := index A B (succ k)
  let x := halfReciprocal U B
  let y := halfReciprocal V B
  let p := harmonicPrefix A B Q (succ k)
  let q := harmonicPrefix A B Q k
  let w := embed (interval (U+B) U Q)
  let r := fraction B U
  have hU := (row_source A B k hs).andE₁
  have hV := le_trans hU (le_add_right U B)
  have hv := index_succ (Γ := Γ) A B k
  have delta : Γ ⊢[PRAAx] qsub p q ≐ w :=
    (harmonic_difference A U V Q).eqTrans (embed_congr (interval_congr hv (.eqRefl _)))
  have t : Γ ⊢[PRAAx] embed (trapezoid U B) ≐ qadd x y :=
    (embed_add _ _).eqTrans
      (qadd_congr (GaussianEulerDecayOrder.fraction_embedding B (two*U) (positive_product _ _ (le_succ_self one) hU))
        ((GaussianEulerDecayOrder.fraction_embedding B (two*(U+B)) (positive_product _ _ (le_succ_self one) hV)).eqTrans
          (half_congr hv.eqSymm)))
  have unfoldRef := (embed_sub (trapezoid U B) (interval (U+B) U Q)).eqTrans (qsub_congr t (.eqRefl _))
  have change : Γ ⊢[PRAAx] qsub (anchor A B Q (succ k)) (anchor A B Q k) ≐ qsub (qsub y x) w :=
    (nested_difference y x p q (embed_canonical _)).eqTrans (qsub_congr (.eqRefl _) delta)
  have addCancel : Γ ⊢[PRAAx] qadd (qadd x x) (qsub y x) ≐ qadd x y :=
    (qadd_associative x x (qsub y x)).eqTrans
      (qadd_congr (.eqRefl _) (GaussianRationalLinearProduct.add_sub_right x y
        (ofGaussian_canonical _ _ (positive_product _ _ (le_succ_self one) (row_source A B (succ k) hs).andE₁))))
  have e : Γ ⊢[PRAAx] qadd r (qsub (anchor A B Q (succ k)) (anchor A B Q k)) ≐ qsub (qadd x y) w :=
    (qadd_congr (half_pair U B hU).eqSymm change).eqTrans
      ((qadd_associative (qadd x x) (qsub y x) (qnegative w)).eqSymm.eqTrans (qsub_congr addCancel (.eqRefl _)))
  exact unfoldRef.eqTrans e.eqSymm

theorem anchor_zero (A B Q : PTm n) (ha : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] anchor A B Q zero ≐ halfReciprocal A B := by
  have iz : Γ ⊢[PRAAx] index A B zero ≐ A := by unfold index; ipra_ring
  have e := (embed_congr (interval_congr (Γ := Γ) (Q := Q) iz (.eqRefl A))).eqTrans (cell_zero A Q (horizon A A Q))
  exact (qsub_congr (half_congr iz) e).eqTrans
    (GaussianRationalReconstruction.qsub_zero_right _ (ofGaussian_canonical _ _ (positive_product _ _ (le_succ_self one) ha)))

end LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliReference
