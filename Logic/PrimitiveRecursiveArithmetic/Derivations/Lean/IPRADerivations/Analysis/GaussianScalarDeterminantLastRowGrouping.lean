import IPRADerivations.Analysis.GaussianScalarDeterminant
import IPRADerivations.Analysis.GaussianRationalPermutationSum
import IPRADerivations.Analysis.GaussianRationalBlockSums
import IPRADerivations.Foundations.RuntimePermutationPacking

/-!
# Grouping the actual determinant terms by the last row

The rectangular rank bijection makes one block for each column paired with
the last row. Within that column's block the terms are read from the actual
retained list by reinserting the maximum label at that column. This groups
the exact scalar Leibniz sum in the original encoding.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarDeterminantLastRowGrouping

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (count words)
open LeanProofs.IPRA.Foundations.RuntimePermutationPacking (grid unpackRank unpack_spec pack_unpack unpack_pack successor_count column minorRank minorWord)
open LeanProofs.IPRA.Foundations.RuntimePermutationFactorialBound (packingF packing_bound)
open LeanProofs.IPRA.Foundations.RuntimePermutationInsertion (insertedWord)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open GaussianRationalFiniteSum (sum sum_index_congr termsEqual)
open GaussianRationalBlockSums (blockTotal sum_blocks)
open GaussianRationalPermutationSum (boundedRange inverseLaw mappedBody)
open GaussianScalarDeterminant (scalarDet signedBody signedTerm rawProduct)
open GaussianPolynomialDeterminantTerms (signPoint)
open GaussianRationalHorner (qmul)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def packBody : PTm 2 := ap2 packingF (var 0) (fstT (var 1))
def unpackBody : PTm 2 := unpackRank (fstT (var 1)) (var 0)
def originalBody (t : PTm 2) : PTm 2 := inst2 t (var 0) (sndT (var 1))
def reorderedBody (t : PTm 2) : PTm 2 := mappedBody (originalBody t) unpackBody
def grouped (t : PTm 2) (m x : PTm n) : PTm n := blockTotal (reorderedBody t) (count m) (succ m) (pairT m x)

theorem pack_body_at (m x i : PTm n) : Γ ⊢[PRAAx] inst2 packBody i (pairT m x) ≐ ap2 packingF i m := by
  simpa [packBody,inst2] using congrAp2 packingF (.eqRefl i) (fst_pair (Γ := Γ) m x)

theorem unpack_body_at (m x i : PTm n) : Γ ⊢[PRAAx] inst2 unpackBody i (pairT m x) ≐ unpackRank m i := by
  simpa [unpackBody,inst2] using Prf.eqCongr (unpackRank (var 0) (var 1) : PTm 2)
    (σ := ![fstT (pairT m x),i]) (σ' := ![m,i]) (fun j => by fin_cases j; exact fst_pair _ _; exact .eqRefl _)

theorem original_body_at (t : PTm 2) (m x i : PTm n) : Γ ⊢[PRAAx] inst2 (originalBody t) i (pairT m x) ≐ inst2 t i x := by
  change Γ ⊢[PRAAx] Syn.subst ![i,pairT m x] (inst2 t (var 0) (sndT (var 1))) ≐ inst2 t i x
  simpa only [subst_inst2,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    congrInst2 t (.eqRefl i) (snd_pair (Γ := Γ) m x)

theorem reordered_body_at (t : PTm 2) (m x i : PTm n) : Γ ⊢[PRAAx]
    inst2 (reorderedBody t) i (pairT m x) ≐ inst2 t (unpackRank m i) x := by
  rw [reorderedBody,GaussianRationalPermutationSum.inst2_mappedBody]
  exact (congrInst2 (originalBody t) (unpack_body_at m x i) (.eqRefl _)).eqTrans (original_body_at t m x _)

theorem pack_range (m x : PTm n) : Γ ⊢[PRAAx] boundedRange packBody (grid m) (pairT m x) := by
  refine .allI (.impI ?_)
  let a := Syn.shift m
  let b := Syn.shift x
  let Δ := lt (var 0) (grid a) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (grid a) := Prf.hyp0
  have actual := packing_bound a (var 0) (lt_congr (.eqRefl _) (successor_count a).eqSymm hi)
  simpa only [Δ,a,b,Syn.shift,subst_pairT,grid,LeanProofs.IPRA.Foundations.RuntimePermutationPacking.subst_grid,
    LeanProofs.IPRA.Foundations.RuntimePermutationWords.subst_count,PTm.subst_mul,ConciseIPRA.PTm.subst_succ] using
    lt_congr (pack_body_at a b (var 0)).eqSymm (.eqRefl _) actual

theorem unpack_range (m x : PTm n) : Γ ⊢[PRAAx] boundedRange unpackBody (grid m) (pairT m x) := by
  refine .allI (.impI ?_)
  let a := Syn.shift m
  let b := Syn.shift x
  let Δ := lt (var 0) (grid a) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (grid a) := Prf.hyp0
  have actual := (unpack_spec a (var 0) hi).andE₁
  simpa only [Δ,a,b,Syn.shift,subst_pairT,LeanProofs.IPRA.Foundations.RuntimePermutationPacking.subst_grid] using
    lt_congr (unpack_body_at a b (var 0)).eqSymm (successor_count a) actual

theorem after_unpack (m x : PTm n) : Γ ⊢[PRAAx] inverseLaw unpackBody packBody (grid m) (pairT m x) := by
  refine .allI (.impI ?_)
  let a := Syn.shift m
  let b := Syn.shift x
  let Δ := lt (var 0) (grid a) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (grid a) := Prf.hyp0
  have atUnpack := unpack_body_at (Γ := Δ) a b (var 0)
  have e := (congrInst2 packBody atUnpack (.eqRefl _)).eqTrans
    ((pack_body_at a b (unpackRank a (var 0))).eqTrans (pack_unpack a (var 0) hi))
  simpa only [Δ,a,b,Syn.shift,subst_pairT,LeanProofs.IPRA.Foundations.RuntimePermutationPacking.subst_grid] using e

theorem after_pack (m x : PTm n) : Γ ⊢[PRAAx] inverseLaw packBody unpackBody (grid m) (pairT m x) := by
  refine .allI (.impI ?_)
  let a := Syn.shift m
  let b := Syn.shift x
  let Δ := lt (var 0) (grid a) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (grid a) := Prf.hyp0
  have exactBound := lt_congr (.eqRefl _) (successor_count a).eqSymm hi
  have e := (congrInst2 unpackBody (pack_body_at a b (var 0)) (.eqRefl _)).eqTrans
    ((unpack_body_at a b (ap2 packingF (var 0) a)).eqTrans (unpack_pack a (var 0) exactBound))
  simpa only [Δ,a,b,Syn.shift,subst_pairT,LeanProofs.IPRA.Foundations.RuntimePermutationPacking.subst_grid] using e

theorem sum_grouped (t : PTm 2) (m x : PTm n) : Γ ⊢[PRAAx] sum t (count (succ m)) x ≐ grouped t m x := by
  have terms : Γ ⊢[PRAAx] termsEqual t (originalBody t) (count (succ m)) x (pairT m x) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,subst_pairT] using (original_body_at t (Syn.shift m) (Syn.shift x) (var 0)).eqSymm
  have orig := GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms
  have sameGrid := sum_index_congr (Γ := Γ) (originalBody t) (successor_count m) (.eqRefl (pairT m x))
  have reorder := GaussianRationalPermutationSum.permutation_sum (Γ := Γ) (originalBody t) unpackBody packBody (grid m) (pairT m x)
    (unpack_range m x) (pack_range m x) (after_unpack m x) (after_pack m x)
  exact orig.eqTrans (sameGrid.eqTrans (reorder.eqSymm.eqTrans (sum_blocks (reorderedBody t) _ _ _)))

private theorem inserted_word_congr (m : PTm n) {p q d e : PTm n}
    (hp : Γ ⊢[PRAAx] p ≐ q) (hd : Γ ⊢[PRAAx] d ≐ e) : Γ ⊢[PRAAx] insertedWord m p d ≐ insertedWord m q e := by
  simpa only [LeanProofs.IPRA.Foundations.RuntimePermutationInsertion.subst_insertedWord,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (insertedWord (var 0) (var 1) (var 2) : PTm 3) (σ := ![m,p,d]) (σ' := ![m,q,e])
      (fun j => by fin_cases j; exact .eqRefl _; exact hp; exact hd)

theorem grouped_word (m p r : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hr : Γ ⊢[PRAAx] lt r (count m)) : Γ ⊢[PRAAx]
    entry (words (succ m)) (unpackRank m (count m*p+r)) ≐ insertedWord m p (entry (words m) r) := by
  let z := count m*p+r
  have commute : Γ ⊢[PRAAx] r+p*count m ≐ z :=
    (add_comm r (p*count m)).eqTrans (congrAdd (mul_comm p (count m)) (.eqRefl r))
  have rectangle : Γ ⊢[PRAAx] lt (r+p*count m) (grid m) :=
    LeanProofs.IPRA.Foundations.MixedRadixExpansion.append_interval hr hp
  have hz : Γ ⊢[PRAAx] lt z (grid m) := lt_congr commute (.eqRefl _) rectangle
  have div := Foundations.RuntimeWordAppend.divide_unique (count m) z p r
    (LeanProofs.IPRA.Foundations.RuntimePermutationWords.words_nonempty m) (.eqRefl _) hr
  have minor : Γ ⊢[PRAAx] minorWord m z ≐ entry (words m) r := Foundations.SequenceComposition.entry_congr (.eqRefl _) div.andE₂
  have col : Γ ⊢[PRAAx] column m z ≐ p := div.andE₁
  exact (unpack_spec m z hz).andE₂.eqTrans (inserted_word_congr m col minor)

theorem determinant_grouped (A m : PTm n) : Γ ⊢[PRAAx] scalarDet A (succ m) ≐ grouped signedBody m (pairT A (succ m)) :=
  (GaussianScalarDeterminant.scalar_leibniz A (succ m)).eqTrans (sum_grouped signedBody m (pairT A (succ m)))

private theorem signed_word_congr (A m : PTm n) {u v : PTm n} (h : Γ ⊢[PRAAx] u ≐ v) : Γ ⊢[PRAAx]
    qmul (signPoint m u) (rawProduct A m u) ≐ qmul (signPoint m v) (rawProduct A m v) := by
  simpa only [GaussianRationalHorner.subst_qmul,GaussianPolynomialDeterminantTerms.subst_signPoint,GaussianScalarDeterminant.subst_rawProduct,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (qmul (signPoint (var 0) (var 1)) (rawProduct (var 2) (var 0) (var 1)) : PTm 3)
      (σ := ![m,u,A]) (σ' := ![m,v,A]) (fun j => by fin_cases j; exact .eqRefl _; exact h; exact .eqRefl _)

theorem signed_grouped_term (A m p r : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hr : Γ ⊢[PRAAx] lt r (count m)) :
    Γ ⊢[PRAAx] inst2 (reorderedBody signedBody) (count m*p+r) (pairT m (pairT A (succ m))) ≐
      qmul (signPoint (succ m) (insertedWord m p (entry (words m) r))) (rawProduct A (succ m) (insertedWord m p (entry (words m) r))) := by
  refine (reordered_body_at signedBody m (pairT A (succ m)) _).eqTrans
    ((GaussianScalarDeterminant.signed_body_at A (succ m) _).eqTrans ?_)
  exact signed_word_congr A (succ m) (grouped_word m p r hp hr)

theorem actual_determinant_last_row_grouped_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (scalarDet (var 0) (succ (var 1)) ≐ grouped signedBody (var 1) (pairT (var 0) (succ (var 1)))) :=
  closeUniv 2 (determinant_grouped _ _)

theorem actual_last_row_grouped_word_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (succ (var 0)) ⟶ lt (var 2) (count (var 0)) ⟶
      entry (words (succ (var 0))) (unpackRank (var 0) (count (var 0)*var 1+var 2)) ≐
        insertedWord (var 0) (var 1) (entry (words (var 0)) (var 2))) :=
  closeUniv 3 (.impI (.impI (grouped_word _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianScalarDeterminantLastRowGrouping
