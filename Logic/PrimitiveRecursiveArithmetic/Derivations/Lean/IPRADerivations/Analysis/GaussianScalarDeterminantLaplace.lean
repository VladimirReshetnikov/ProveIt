import IPRADerivations.Analysis.GaussianScalarDeterminantLastRowGrouping
import IPRADerivations.Analysis.GaussianScalarDeterminantLastRowProduct
import IPRADerivations.Analysis.GaussianScalarColumnSelection
import IPRADerivations.Foundations.RuntimePermutationInsertionParity

/-!
# The last-row cofactor factors of the actual determinant

The numerical inversion bit determines a Gaussian-rational unit. In each
last-row block the insertion changes this sign by the cofactor sign, and
the product splits through the actual ordered column-deleted matrix.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarDeterminantLaplace

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.PTm (monus)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_zero sel_one)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (inversions count words parity)
open LeanProofs.IPRA.Foundations.RuntimePermutationInsertion (insertedWord)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open GaussianRationalHorner (qmul canonical)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open GaussianRationalMetric (qnegative qnegative_canonical)
open GaussianRationalPowerAlgebra (qmul_commutative qmul_shuffle)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianPolynomialDeterminantTerms (cell signPoint)
open GaussianScalarDeterminant (signedBody signedTerm rawProduct scalarDet)
open GaussianScalarDeterminantLastRowGrouping (reorderedBody grouped signed_grouped_term determinant_grouped)
open GaussianScalarDeterminantLastRowProduct (minorTable last_row_product)
open GaussianRationalFiniteSum (sum termsEqual multiplyBody multiply_body_at sum_multiply)
open GaussianRationalBlockSums (blockBody block_body_at)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def signBit (b : PTm n) : PTm n := sel b (qnegative qone) qone
def unitSign (k : PTm n) : PTm n := signBit (par k)
def rowWeight (A m p : PTm n) : PTm n := qmul (unitSign (m+p)) (cell A m p)
def summand (A m p : PTm n) : PTm n := qmul (rowWeight A m p) (scalarDet (minorTable A m p) m)
def expansionBody : PTm 2 := summand (fstT (var 1)) (sndT (var 1)) (var 0)
def expansion (A m : PTm n) : PTm n := GaussianRationalFiniteSum.sum expansionBody (succ m) (pairT A m)
def signTerms (m p : PTm n) : Fm PTm n := .all
  (lt (var 0) (count (Syn.shift m)) ⟶
    let a := Syn.shift m
    let b := Syn.shift p
    let d := entry (words a) (var 0)
    parity (succ a) (insertedWord a b d) ≐ par (inversions a d+(a+b)))
def allSigns (m : PTm n) : Fm PTm n := .all (lt (var 0) (succ (Syn.shift m)) ⟶ signTerms (Syn.shift m) (var 0))

@[simp] theorem subst_unitSign {k : ℕ} (σ : Fin n → PTm k) (i : PTm n) :
    Syn.subst σ (unitSign i) = unitSign (Syn.subst σ i) := by simp [unitSign,signBit,sel,par,one]
@[simp] theorem subst_summand {k : ℕ} (σ : Fin n → PTm k) (A m p : PTm n) :
    Syn.subst σ (summand A m p) = summand (Syn.subst σ A) (Syn.subst σ m) (Syn.subst σ p) := by simp [summand,rowWeight]
@[simp] theorem subst_signTerms {k : ℕ} (σ : Fin n → PTm k) (m p : PTm n) :
    (signTerms m p).subst σ = signTerms (Syn.subst σ m) (Syn.subst σ p) := by
  simp [signTerms,Syn.subst_shift,Syn.shift_subst,par]
@[simp] theorem subst_allSigns {k : ℕ} (σ : Fin n → PTm k) (m : PTm n) :
    (allSigns m).subst σ = allSigns (Syn.subst σ m) := by simp [allSigns,Syn.subst_shift,Syn.shift_subst]

theorem sign_bit_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] signBit a ≐ signBit b := by
  simpa [signBit,sel,one] using Prf.eqCongr (signBit (var 0) : PTm 1) (σ := ![a]) (σ' := ![b]) (fun j => by fin_cases j; exact h)

theorem sign_bit_even (b : PTm n) (h : Γ ⊢[PRAAx] b ≐ zero) : Γ ⊢[PRAAx] signBit b ≐ qone := sel_zero h
theorem sign_bit_odd (b : PTm n) (h : Γ ⊢[PRAAx] b ≐ one) : Γ ⊢[PRAAx] signBit b ≐ qnegative qone := sel_one h

theorem unit_sign_canonical (k : PTm n) : Γ ⊢[PRAAx] canonical (unitSign k) := by
  refine .orE (par_cases k) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr (sign_bit_even (par k) Prf.hyp0) qone_canonical
  · exact GaussianRationalHorner.canonical_congr (sign_bit_odd (par k) Prf.hyp0)
      (qnegative_canonical _)

private theorem par_twice (a : PTm n) : Γ ⊢[PRAAx] par (par a) ≐ par a := by
  refine .orE (par_cases a) ?_ ?_
  · exact ((congrAp1 parF Prf.hyp0).eqTrans par_zero).eqTrans Prf.hyp0.eqSymm
  · have oddOne : (par a ≐ one) :: Γ ⊢[PRAAx] par one ≐ one :=
      (par_succ zero).eqTrans ((congrMonus (.eqRefl one) par_zero).eqTrans (monus_zero one))
    exact ((congrAp1 parF Prf.hyp0).eqTrans oddOne).eqTrans Prf.hyp0.eqSymm

theorem unit_sign_add (a b : PTm n) : Γ ⊢[PRAAx] unitSign (a+b) ≐ qmul (unitSign a) (unitSign b) := by
  refine .orE (par_cases b) ?_ ?_
  · have hb : (par b ≐ zero) :: Γ ⊢[PRAAx] par b ≐ zero := Prf.hyp0
    exact (sign_bit_congr (par_add_even a hb)).eqTrans
      ((qmul_one_right (unitSign a) (unit_sign_canonical a)).eqSymm.eqTrans
        (qmul_congr (.eqRefl _) (sign_bit_even (par b) hb).eqSymm))
  · let Δ := (par b ≐ one) :: Γ
    have hb : Δ ⊢[PRAAx] par b ≐ one := Prf.hyp0
    have flip : Δ ⊢[PRAAx] par (a+b) ≐ monus one (par a) :=
      (par_add a b).eqTrans ((congrAp1 parF ((congrAdd (.eqRefl (par a)) hb).eqTrans (succ_eq_add_one _).eqSymm)).eqTrans
        ((par_succ _).eqTrans (congrMonus (.eqRefl one) (par_twice a))))
    refine .orE (par_cases a) ?_ ?_
    · have ha : (par a ≐ zero) :: Δ ⊢[PRAAx] par a ≐ zero := Prf.hyp0
      have p := flip.wk.eqTrans ((congrMonus (.eqRefl one) ha).eqTrans (monus_zero one))
      have negativeCanonical := qnegative_canonical (Γ := (par a ≐ zero) :: Δ) (qone : PTm n)
      have identity := (qmul_commutative qone (qnegative qone)).eqTrans (qmul_one_right _ negativeCanonical)
      exact (sign_bit_odd _ p).eqTrans (identity.eqSymm.eqTrans
        (qmul_congr (sign_bit_even _ ha).eqSymm (sign_bit_odd _ hb.wk).eqSymm))
    · have ha : (par a ≐ one) :: Δ ⊢[PRAAx] par a ≐ one := Prf.hyp0
      have p := flip.wk.eqTrans ((congrMonus (.eqRefl one) ha).eqTrans (monus_self one))
      have square : (par a ≐ one) :: Δ ⊢[PRAAx] qmul (qnegative qone) (qnegative qone) ≐ qone :=
        (GaussianScalarColumnSelection.negative_both_product qone qone).eqTrans (qmul_one_right _ qone_canonical)
      exact (sign_bit_even _ p).eqTrans (square.eqSymm.eqTrans
        (qmul_congr (sign_bit_odd _ ha).eqSymm (sign_bit_odd _ hb.wk).eqSymm))

theorem inserted_sign (m p d : PTm n)
    (h : Γ ⊢[PRAAx] parity (succ m) (insertedWord m p d) ≐ par (inversions m d+(m+p))) : Γ ⊢[PRAAx]
    signPoint (succ m) (insertedWord m p d) ≐ qmul (unitSign (m+p)) (signPoint m d) :=
  (sign_bit_congr h).eqTrans ((unit_sign_add (inversions m d) (m+p)).eqTrans (qmul_commutative _ _))

theorem term_factored (A m p r : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hr : Γ ⊢[PRAAx] lt r (count m))
    (h : Γ ⊢[PRAAx] parity (succ m) (insertedWord m p (entry (words m) r)) ≐ par (inversions m (entry (words m) r)+(m+p))) :
    Γ ⊢[PRAAx] inst2 (reorderedBody signedBody) (count m*p+r) (pairT m (pairT A (succ m))) ≐
      qmul (rowWeight A m p) (signedTerm (minorTable A m p) m r) := by
  let d := entry (words m) r
  have product := last_row_product A m p d hp
  have sign := inserted_sign m p d h
  exact (signed_grouped_term A m p r hp hr).eqTrans
    ((qmul_congr sign product).eqTrans (qmul_shuffle (unitSign (m+p)) (signPoint m d) (cell A m p) (rawProduct (minorTable A m p) m d)))

theorem sign_term_at (m p r : PTm n) (h : Γ ⊢[PRAAx] signTerms m p) (hr : Γ ⊢[PRAAx] lt r (count m)) :
    Γ ⊢[PRAAx] parity (succ m) (insertedWord m p (entry (words m) r)) ≐ par (inversions m (entry (words m) r)+(m+p)) := by
  have rule : Γ ⊢[PRAAx] lt r (count m) ⟶ parity (succ m) (insertedWord m p (entry (words m) r)) ≐
      par (inversions m (entry (words m) r)+(m+p)) := by
    simpa [signTerms,par] using h.allE r
  exact .impE rule hr

theorem sign_block_at (m p : PTm n) (h : Γ ⊢[PRAAx] allSigns m) (hp : Γ ⊢[PRAAx] lt p (succ m)) :
    Γ ⊢[PRAAx] signTerms m p := by
  have rule : Γ ⊢[PRAAx] lt p (succ m) ⟶ signTerms m p := by simpa [allSigns] using h.allE p
  exact .impE rule hp

theorem expansion_body_at (A m p : PTm n) : Γ ⊢[PRAAx] inst2 expansionBody p (pairT A m) ≐ summand A m p := by
  simpa only [expansionBody,inst2,subst_summand,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (summand (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![fstT (pairT A m),sndT (pairT A m),p]) (σ' := ![A,m,p])
      (fun j => by fin_cases j; exact fst_pair _ _; exact snd_pair _ _; exact .eqRefl _)

theorem block_expansion (A m p : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (h : Γ ⊢[PRAAx] signTerms m p) :
    Γ ⊢[PRAAx] inst2 (blockBody (reorderedBody signedBody)) p (pairT (count m) (pairT m (pairT A (succ m)))) ≐ summand A m p := by
  let t := reorderedBody signedBody
  let x := pairT m (pairT A (succ m))
  let y := pairT (minorTable A m p) m
  let a := rowWeight A m p
  have terms : Γ ⊢[PRAAx] termsEqual (offB t) (multiplyBody signedBody) (count m) (pairT (count m*p) x) (pairT a y) := by
    refine .allI (.impI ?_)
    let A' := Syn.shift A
    let m' := Syn.shift m
    let p' := Syn.shift p
    let Δ := lt (var 0) (count m') :: Γ.map Fm.shift
    have hp' : Δ ⊢[PRAAx] lt p' (succ m') := by
      simpa only [Δ,p',m',Fm.shift,Syn.shift,subst_lt,ConciseIPRA.PTm.subst_succ] using hp.shift.wk
    have h' : Δ ⊢[PRAAx] signTerms m' p' := by
      simpa only [Δ,p',m',Fm.shift,Syn.shift,subst_signTerms] using h.shift.wk
    have hr : Δ ⊢[PRAAx] lt (var 0) (count m') := Prf.hyp0
    have cellEq := term_factored A' m' p' (var 0) hp' hr (sign_term_at m' p' (var 0) h' hr)
    have left := GaussianRationalFiniteProduct.offset_at (Γ := Δ) t (count m'*p') (var 0) (pairT m' (pairT A' (succ m')))
    have right := (multiply_body_at (Γ := Δ) signedBody (rowWeight A' m' p') (var 0) (pairT (minorTable A' m' p') m')).eqTrans
      (qmul_congr (.eqRefl _) (GaussianScalarDeterminant.signed_body_at (minorTable A' m' p') m' (var 0)))
    simpa [Δ,t,x,y,a,A',m',p',rowWeight,Syn.shift] using left.eqTrans (cellEq.eqTrans right.eqSymm)
  have inner := GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms
  exact (block_body_at t (count m) p x).eqTrans (inner.eqTrans
    ((sum_multiply signedBody a (count m) y).eqTrans (qmul_congr (.eqRefl a)
      (GaussianScalarDeterminant.scalar_leibniz (minorTable A m p) m).eqSymm)))

theorem expansion_from_signs (A m : PTm n) (h : Γ ⊢[PRAAx] allSigns m) : Γ ⊢[PRAAx] scalarDet A (succ m) ≐ expansion A m := by
  refine (determinant_grouped A m).eqTrans (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ ?_)
  refine .allI (.impI ?_)
  let m' := Syn.shift m
  let A' := Syn.shift A
  let Δ := lt (var 0) (succ m') :: Γ.map Fm.shift
  have hp : Δ ⊢[PRAAx] lt (var 0) (succ m') := Prf.hyp0
  have sign : Δ ⊢[PRAAx] allSigns m' := by simpa only [Δ,m',Fm.shift,Syn.shift,subst_allSigns] using h.shift.wk
  have block := block_expansion A' m' (var 0) hp (sign_block_at m' (var 0) sign hp)
  simpa only [Δ,A',m',Syn.shift,subst_pairT,LeanProofs.IPRA.Foundations.RuntimePermutationWords.subst_count,ConciseIPRA.PTm.subst_succ] using
    block.eqTrans (expansion_body_at A' m' (var 0)).eqSymm

theorem original_signs (m : PTm n) : Γ ⊢[PRAAx] allSigns m := by
  refine .allI (.impI (.allI (.impI ?_)))
  let m' := Syn.shift (Syn.shift m)
  let Δ := lt (var 0) (count m') :: (lt (var 0) (succ (Syn.shift m)) :: Γ.map Fm.shift).map Fm.shift
  have hp : Δ ⊢[PRAAx] lt (var 1) (succ m') := by
    simpa only [Δ,m',List.map_cons,Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using
      (Prf.hyp1 : Δ ⊢[PRAAx] (lt (var 0) (succ (Syn.shift m))).shift)
  exact LeanProofs.IPRA.Foundations.RuntimePermutationInsertionParity.inserted_parity_plus m' (var 1)
    (entry (words m') (var 0)) hp

theorem last_row_expansion (A m : PTm n) : Γ ⊢[PRAAx] scalarDet A (succ m) ≐ expansion A m :=
  expansion_from_signs A m (original_signs m)

def expansionF : PR 2 := PTm.toPR (expansion (var 0) (var 1))
def run (A m : PTm n) : PTm n := ap2 expansionF A m

@[simp] theorem subst_expansion {k : ℕ} (σ : Fin n → PTm k) (A m : PTm n) :
    Syn.subst σ (expansion A m) = expansion (Syn.subst σ A) (Syn.subst σ m) := by simp [expansion]

theorem program_at (A m : PTm n) : Γ ⊢[PRAAx] run A m ≐ expansion A m := by
  simpa [expansionF,run,ap2] using toPR_eq (Γ := Γ) (expansion (var 0) (var 1) : PTm 2) ![A,m]

theorem actual_last_row_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (scalarDet (var 0) (succ (var 1)) ≐ expansion (var 0) (var 1)) := closeUniv 2 (last_row_expansion _ _)

theorem actual_returned_last_row_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (scalarDet (var 0) (succ (var 1)) ≐ run (var 0) (var 1)) :=
  closeUniv 2 ((last_row_expansion _ _).eqTrans (program_at _ _).eqSymm)

end LeanProofs.IPRA.Analysis.GaussianScalarDeterminantLaplace
