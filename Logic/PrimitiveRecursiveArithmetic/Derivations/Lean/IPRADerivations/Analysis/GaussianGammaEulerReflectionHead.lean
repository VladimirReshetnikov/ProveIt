import IPRADerivations.Analysis.GaussianGammaEulerHeadLower
import IPRADerivations.Analysis.GaussianRationalPowerAlgebra

/-!
# Paired Euler heads and the finite sine product

Pair the factors of the original Euler polynomial heads at z/B and −z/B.
The result is −(z/B)² times the literal finite product of
1−(z/(Bk))². The cleared equality holds even when one of the heads is
zero. At apart inputs the exact rational reciprocals satisfy the
corresponding cleared reflection identity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerReflectionHead

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaEulerHead (factor head run head_zero head_succ program_at)
open GaussianGammaEulerHeadLower (translated factor_represents)
open GaussianRationalFiniteProduct (qprod product_succ product_zero)
open GaussianRationalHorner (ofGaussian qmul ofGaussian_represents positive_product represents_congr
  canonical_unique qmul_represents qmul_canonical)
open GaussianRationalMetric (qnegative qsub qnegative_canonical qsub_canonical qnegative_represents qsub_represents)
open GaussianRationalPowerAlgebra (qmul_shuffle)
open GaussianRationalReciprocal (qone qone_represents_scaled normNumerator reciprocal reciprocal_identity)
open GaussianRationalSyntheticDivision (qmul_congr qone_canonical)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRootAlgebra (equal_of_values re_add im_add re_mul im_mul re_scale im_scale re_one im_one re_neg im_neg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def squareFactor (i z B : PTm n) : PTm n :=
  qsub qone (qmul (ofGaussian z (B*succ i)) (ofGaussian z (B*succ i)))

def body : PTm 2 := squareFactor (var 0) (fstT (var 1)) (sndT (var 1))

def sineProduct (z B N : PTm n) : PTm n := qprod body N (pairT z B)

def negativeSquare (z B : PTm n) : PTm n := qnegative (qmul (ofGaussian z B) (ofGaussian z B))

def denominator (z B N : PTm n) : PTm n := qmul (negativeSquare z B) (sineProduct z B N)

@[simp] theorem subst_squareFactor {l : ℕ} (σ : Fin n → PTm l) (i z B : PTm n) :
    Syn.subst σ (squareFactor i z B) = squareFactor (Syn.subst σ i) (Syn.subst σ z) (Syn.subst σ B) := by
  simp [squareFactor]

@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (z B N : PTm n) :
    Syn.subst σ (denominator z B N) = denominator (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [denominator,negativeSquare,sineProduct]

theorem square_factor_at (i z B : PTm n) :
    Γ ⊢[PRAAx] inst2 body i (pairT z B) ≐ squareFactor i z B := by
  simpa only [body,inst2,subst_squareFactor,Syn.subst_var,subst_fstT,subst_sndT,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (squareFactor (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![i,fstT (pairT z B),sndT (pairT z B)]) (σ' := ![i,z,B])
      (fun j => by fin_cases j; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _)

theorem paired_factor (i z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (factor i z B) (factor i (ComplexLogarithmRemainder.neg z) B) ≐ squareFactor i z B := by
  let E := B*succ i
  have hE : Γ ⊢[PRAAx] le one E := positive_product _ _ hB (zero_lt_succ i)
  have hE2 := positive_product E E hE hE
  have zRep := ofGaussian_represents (Γ := Γ) z E hE
  have zSquared := qmul_represents _ _ _ _ _ _ hE hE zRep zRep
  have left := qmul_represents _ _ _ _ _ _ hE hE (factor_represents i z B hB) (factor_represents i (ComplexLogarithmRemainder.neg z) B hB)
  have right := qsub_represents _ _ _ _ _ hE2 (qone_represents_scaled (E*E)) zSquared
  apply canonical_unique _ _ _ (E*E) (qmul_canonical _ _) (qsub_canonical _ _) hE2 (hrv := right)
  refine represents_congr (.eqRefl _) ?_ (.eqRefl _) left
  apply equal_of_values <;>
    simp only [GaussianRootAlgebra.sub,translated,E,re_mul,im_mul,re_add,im_add,re_scale,im_scale,
      re_one,im_one,re_neg,im_neg] <;> ipra_simps <;> ring

theorem paired_argument (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (ofGaussian z B) (ofGaussian (ComplexLogarithmRemainder.neg z) B) ≐ negativeSquare z B := by
  have zz := ofGaussian_represents (Γ := Γ) z B hB
  have left := qmul_represents _ _ _ _ _ _ hB hB zz (ofGaussian_represents (ComplexLogarithmRemainder.neg z) B hB)
  have right := qnegative_represents _ _ _ (qmul_represents _ _ _ _ _ _ hB hB zz zz)
  apply canonical_unique _ _ _ (B*B) (qmul_canonical _ _) (qnegative_canonical _)
    (positive_product B B hB hB) (hrv := right)
  refine represents_congr (.eqRefl _) ?_ (.eqRefl _) left
  apply equal_of_values <;> simp only [re_mul,im_mul,re_neg,im_neg] <;> ring

theorem denominator_zero (z B : PTm n) : Γ ⊢[PRAAx] denominator z B zero ≐ negativeSquare z B :=
  (qmul_congr (.eqRefl _) (product_zero body (pairT z B))).eqTrans
    (qmul_one_right _ (qnegative_canonical _))

theorem denominator_succ (z B N : PTm n) :
    Γ ⊢[PRAAx] denominator z B (succ N) ≐ qmul (denominator z B N) (squareFactor N z B) :=
  (qmul_congr (.eqRefl _) ((product_succ body N (pairT z B)).eqTrans
    (qmul_congr (.eqRefl _) (square_factor_at N z B)))).eqTrans
    (qmul_associative _ _ _).eqSymm

def pairingLaw (z B N : PTm n) : Fm PTm n := qmul (head z B N) (head (ComplexLogarithmRemainder.neg z) B N) ≐ denominator z B N

@[simp] theorem subst_pairingLaw {l : ℕ} (σ : Fin n → PTm l) (z B N : PTm n) :
    (pairingLaw z B N).subst σ = pairingLaw (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [pairingLaw]

theorem pairing_zero (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] pairingLaw z B zero :=
  (qmul_congr (head_zero z B hB) (head_zero (ComplexLogarithmRemainder.neg z) B hB)).eqTrans
    ((paired_argument z B hB).eqTrans (denominator_zero z B).eqSymm)

theorem pairing_succ (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ih : Γ ⊢[PRAAx] pairingLaw z B N) : Γ ⊢[PRAAx] pairingLaw z B (succ N) :=
  (qmul_congr (head_succ z B N) (head_succ (ComplexLogarithmRemainder.neg z) B N)).eqTrans
    ((qmul_shuffle _ _ _ _).eqTrans
      ((qmul_congr ih (paired_factor N z B hB)).eqTrans (denominator_succ z B N).eqSymm))

theorem paired_heads (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] pairingLaw z B N := by
  have hB' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have law : Γ ⊢[PRAAx] .all (pairingLaw (Syn.shift z) (Syn.shift B) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_pairingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using pairing_zero z B hB
    · simpa only [subst_pairingLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        pairing_succ (Syn.shift z) (Syn.shift B) (var 0) hB'.wk Prf.hyp0
  simpa only [subst_pairingLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using law.allE N

theorem returned_pairing (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul (run z B N) (run (ComplexLogarithmRemainder.neg z) B N) ≐ denominator z B N :=
  (qmul_congr (program_at _ _ _) (program_at _ _ _)).eqTrans (paired_heads z B N hB)

theorem reciprocal_pairing (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hpos : Γ ⊢[PRAAx] le one (normNumerator (run z B N)))
    (hneg : Γ ⊢[PRAAx] le one (normNumerator (run (ComplexLogarithmRemainder.neg z) B N))) : Γ ⊢[PRAAx]
    qmul (denominator z B N) (qmul (reciprocal (run z B N)) (reciprocal (run (ComplexLogarithmRemainder.neg z) B N))) ≐ qone :=
  (qmul_congr (returned_pairing z B N hB).eqSymm (.eqRefl _)).eqTrans
    ((qmul_shuffle _ _ _ _).eqTrans
      ((qmul_congr (reciprocal_identity _ hpos) (reciprocal_identity _ hneg)).eqTrans
        (qmul_one_right _ qone_canonical)))

theorem original_paired_Euler_heads_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ qmul (run (var 0) (var 1) (var 2)) (run (ComplexLogarithmRemainder.neg (var 0)) (var 1) (var 2)) ≐
      denominator (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.impI (returned_pairing _ _ _ Prf.hyp0))

theorem original_paired_Euler_head_inverses_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le one (normNumerator (run (var 0) (var 1) (var 2))) ⟶
      le one (normNumerator (run (ComplexLogarithmRemainder.neg (var 0)) (var 1) (var 2))) ⟶
      qmul (denominator (var 0) (var 1) (var 2))
        (qmul (reciprocal (run (var 0) (var 1) (var 2))) (reciprocal (run (ComplexLogarithmRemainder.neg (var 0)) (var 1) (var 2)))) ≐ qone) :=
  closeUniv 3 (.impI (.impI (.impI (reciprocal_pairing _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerReflectionHead
