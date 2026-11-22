import IPRADerivations.Foundations.RuntimePermutationInsertion
import IPRADerivations.Foundations.RuntimePermutationFactorialBound

/-!
# Exact rectangular indexing of the actual retained permutation list

The original packing records the maximum-label position and rank of its
deleted word. Its actual inverse reads those coordinates by Euclidean
division and inserts the maximum label back at the prescribed position.
Finite injection counting in both directions gives the exact successor
count of the stored list and identifies it with the numerical factorial.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.RuntimePermutationPacking

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero succ)
open RuntimePermutationWords (count words position horizon permutationBit)
open RuntimePermutationDeletion (packed maximumPosition deletedWord deletedRank deleted_rank_correct)
open RuntimePermutationInsertion (inserted insertedWord inserted_tuple inserted_word_bound inserted_word_valid inserted_maximum deleted_inserted_word)
open RuntimePermutationFactorialBound (packingF packing_at packing_bound packing_unique successor_count_bound factorial factorial_zero factorial_succ)
open RuntimeAdjacentPermutationSwap (different_of_lt)
open MasterCertificate (entry)
open SequenceComposition (entry_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def grid (m : PTm n) : PTm n := count m * succ m
def column (m z : PTm n) : PTm n := quo z (count m)
def minorRank (m z : PTm n) : PTm n := rem z (count m)
def minorWord (m z : PTm n) : PTm n := entry (words m) (minorRank m z)
def unpackRank (m z : PTm n) : PTm n := position (inserted m (column m z) (minorWord m z)) (succ m)
def unpackF : PR 2 := PTm.toPR (unpackRank (var 1) (var 0))

@[simp] theorem subst_grid {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) : Syn.subst σ (grid m) = grid (Syn.subst σ m) := by
  simp [grid]

@[simp] theorem subst_unpackRank {l : ℕ} (σ : Fin n → PTm l) (m z : PTm n) :
    Syn.subst σ (unpackRank m z) = unpackRank (Syn.subst σ m) (Syn.subst σ z) := by
  simp [unpackRank,column,minorWord,minorRank,RuntimePermutationWords.position]

theorem unpack_at (m z : PTm n) : Γ ⊢[PRAAx] ap2 unpackF z m ≐ unpackRank m z := by
  simpa [unpackF,ap2] using toPR_eq (Γ := Γ) (unpackRank (var 1) (var 0) : PTm 2) ![z,m]

theorem column_bound (m z : PTm n) (hz : Γ ⊢[PRAAx] lt z (grid m)) : Γ ⊢[PRAAx] lt (column m z) (succ m) :=
  AnalyticNumberTheory.Multiplicative.quo_lt (RuntimeWordAppend.positive_form _ (RuntimePermutationWords.words_nonempty m)) hz

theorem minor_rank_bound (m z : PTm n) : Γ ⊢[PRAAx] lt (minorRank m z) (count m) :=
  (RuntimeWordAppend.divide_spec (count m) z (RuntimePermutationWords.words_nonempty m)).andE₂

theorem minor_bound (m z : PTm n) : Γ ⊢[PRAAx] lt (minorWord m z) (horizon m) :=
  RuntimePermutationWords.retained_bound _ _ (minor_rank_bound m z)

theorem minor_valid (m z : PTm n) : Γ ⊢[PRAAx] permutationBit m (minorWord m z) ≐ one :=
  (RuntimePermutationWords.checker_reflection _ _).iffMpr (RuntimePermutationWords.retained_valid _ _ (minor_rank_bound m z))

theorem unpack_spec (m z : PTm n) (hz : Γ ⊢[PRAAx] lt z (grid m)) : Γ ⊢[PRAAx]
    lt (unpackRank m z) (count (succ m)) ⋏
      entry (words (succ m)) (unpackRank m z) ≐ insertedWord m (column m z) (minorWord m z) :=
  RuntimePermutationWords.listed _ _ (inserted_tuple _ _ _ (column_bound m z hz) (minor_valid m z))

theorem packed_congr (m : PTm n) {u v : PTm n} (h : Γ ⊢[PRAAx] u ≐ v) : Γ ⊢[PRAAx] packed m u ≐ packed m v := by
  simpa only [RuntimePermutationDeletion.subst_packed,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (packed (var 0) (var 1) : PTm 2) (σ := ![m,u]) (σ' := ![m,v])
      (fun j => by fin_cases j; exact .eqRefl _; exact h)

theorem pack_unpack (m z : PTm n) (hz : Γ ⊢[PRAAx] lt z (grid m)) : Γ ⊢[PRAAx] ap2 packingF (unpackRank m z) m ≐ z := by
  let p := column m z
  let d := minorWord m z
  let w := insertedWord m p d
  have hp := column_bound m z hz
  have hd := minor_valid (Γ := Γ) m z
  have hw := inserted_word_bound m p d hp
  have valid := inserted_word_valid m p d hp hd
  have oldRank := deleted_rank_correct m w hw valid
  have deletion := deleted_inserted_word m p d hp hd (minor_bound m z)
  have rankExact : Γ ⊢[PRAAx] deletedRank m w ≐ minorRank m z :=
    RuntimePermutationWords.retained_position_unique m _ _ oldRank.andE₁ (minor_rank_bound m z) (oldRank.andE₂.eqTrans deletion)
  have packedValue : Γ ⊢[PRAAx] packed m w ≐ minorRank m z + p * count m :=
    congrAdd rankExact (congrMul (inserted_maximum m p d hp hd) (.eqRefl _))
  have commute : Γ ⊢[PRAAx] minorRank m z + p * count m ≐ count m * p + minorRank m z := by ipra_ring
  have div := RuntimeWordAppend.divide_spec (count m) z (RuntimePermutationWords.words_nonempty (Γ := Γ) m)
  exact (packing_at m (unpackRank m z)).eqTrans ((packed_congr m (unpack_spec m z hz).andE₂).eqTrans
    (packedValue.eqTrans (commute.eqTrans div.andE₁.eqSymm)))

theorem unpack_pack (m r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count (succ m))) : Γ ⊢[PRAAx]
    unpackRank m (ap2 packingF r m) ≐ r := by
  have bound := packing_bound m r hr
  exact packing_unique m _ r (unpack_spec m _ bound).andE₁ hr (pack_unpack m _ bound)

theorem unpack_different (m u v : PTm n) (hu : Γ ⊢[PRAAx] lt u (grid m)) (hv : Γ ⊢[PRAAx] lt v (grid m))
    (hne : Γ ⊢[PRAAx] neg (u ≐ v)) : Γ ⊢[PRAAx] neg (ap2 unpackF u m ≐ ap2 unpackF v m) := by
  refine .impI (.impE hne.wk ?_)
  have e : (ap2 unpackF u m ≐ ap2 unpackF v m) :: Γ ⊢[PRAAx] unpackRank m u ≐ unpackRank m v :=
    (unpack_at m u).wk.eqSymm.eqTrans (Prf.hyp0.eqTrans (unpack_at m v).wk)
  exact (pack_unpack m u hu).wk.eqSymm.eqTrans ((congrAp2 packingF e (.eqRefl _)).eqTrans (pack_unpack m v hv).wk)

theorem grid_count_bound (m : PTm n) : Γ ⊢[PRAAx] le (grid m) (count (succ m)) := by
  apply Topology.InjectionBound.injection_bound unpackF (d := grid m) (m := count (succ m)) (x := m)
  · refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (grid m)) :: Γ.map Fm.shift
    have h : Δ ⊢[PRAAx] lt (var 0) (grid (Syn.shift m)) := by
      simpa only [Δ,Syn.shift,subst_grid] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (grid m)))
    simpa only [Δ,Syn.shift,RuntimePermutationWords.subst_count,ConciseIPRA.PTm.subst_succ] using
      lt_congr (unpack_at (Syn.shift m) (var 0)).eqSymm (.eqRefl _) (unpack_spec _ _ h).andE₁
  · refine .allI (.allI (.impI (.impI ?_)))
    let m' := Syn.shift (Syn.shift m)
    let Δ := lt (var 0) (Syn.shift (Syn.shift (grid m))) :: lt (var 1) (var 0) :: (Γ.map Fm.shift).map Fm.shift
    have hv : Δ ⊢[PRAAx] lt (var 0) (grid m') := by
      simpa only [Δ,m',Syn.shift,subst_grid] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift (grid m))))
    have hu : Δ ⊢[PRAAx] lt (var 1) (grid m') := lt_of_lt_of_le Prf.hyp1 (le_of_lt hv)
    exact unpack_different m' (var 1) (var 0) hu hv (different_of_lt Prf.hyp1)

theorem successor_count (m : PTm n) : Γ ⊢[PRAAx] count (succ m) ≐ grid m :=
  le_antisymm (successor_count_bound m) (grid_count_bound m)

theorem count_factorial (m : PTm n) : Γ ⊢[PRAAx] count m ≐ factorial m := by
  have all : Γ ⊢[PRAAx] .all (count (var 0) ≐ factorial (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq,RuntimePermutationWords.subst_count,RuntimePermutationFactorialBound.subst_factorial,Syn.subst_var,Syn.inst_zero]
      exact RuntimePermutationWords.count_zero.eqTrans factorial_zero.eqSymm
    · simp only [Fm.subst_eq,RuntimePermutationWords.subst_count,RuntimePermutationFactorialBound.subst_factorial,Syn.subst_var,Syn.repl_zero]
      exact (successor_count (var 0)).eqTrans ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (factorial_succ (var 0)).eqSymm)
  simpa only [Fm.subst_eq,RuntimePermutationWords.subst_count,RuntimePermutationFactorialBound.subst_factorial,Syn.subst_var,Syn.inst_zero] using all.allE m

theorem actual_permutation_packing_roundtrip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (grid (var 0)) ⟶ ap2 packingF (unpackRank (var 0) (var 1)) (var 0) ≐ var 1) :=
  closeUniv 2 (.impI (pack_unpack _ _ Prf.hyp0))

theorem actual_permutation_unpacking_roundtrip_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (count (succ (var 0))) ⟶ unpackRank (var 0) (ap2 packingF (var 1) (var 0)) ≐ var 1) :=
  closeUniv 2 (.impI (unpack_pack _ _ Prf.hyp0))

theorem actual_permutation_successor_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (count (succ (var 0)) ≐ grid (var 0)) := closeUniv 1 (successor_count _)

theorem actual_retained_permutation_factorial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (count (var 0) ≐ factorial (var 0)) := closeUniv 1 (count_factorial _)

theorem actual_permutation_unpacking_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 unpackF (var 1) (var 0) ≐ unpackRank (var 0) (var 1)) := closeUniv 2 (unpack_at _ _)

end LeanProofs.IPRA.Foundations.RuntimePermutationPacking
