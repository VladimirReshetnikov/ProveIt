import IPRADerivations.Foundations.FiniteHausdorff
import IPRADerivations.Core.Header

/-!
# Concatenation of actual finite Hausdorff lists

Finite-demand `lem:aggregate-calculus`, clause two. The append program is the
actual checked sequence constructor. Its entries and the actual nearest-index
program provide the two branch witnesses; no concatenation cover or distance
estimate is supplied as a premise. Repeated entries are allowed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteHausdorffConcat

open_ipra
open LeanProofs.IPRA.Foundations.FiniteHausdorff
open LeanProofs.IPRA.Foundations.SequenceComposition
  (length append append_length append_left append_right append_right_at add_lt_left)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.DemandClosure (maximum maximum_left maximum_right maximum_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem suffix_range {i a b : PTm n} (ha : Γ ⊢[PRAAx] le a i)
    (hi : Γ ⊢[PRAAx] lt i (a + b)) : Γ ⊢[PRAAx] lt (monus i a) b := by
  have e : Γ ⊢[PRAAx] succ i ≐ succ (monus i a) + a :=
    (congrSucc (eq_add_of_le ha)).eqTrans (by ipra_ring)
  exact le_of_add_le_add_right (le_congr e (add_comm _ _) hi)

theorem left_range (T T' j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length T)) :
    Γ ⊢[PRAAx] lt j (length (append T T')) :=
  lt_congr (.eqRefl _) (append_length T T').eqSymm
    (lt_of_lt_of_le hj (le_add_right _ _))

theorem right_range (T T' j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length T')) :
    Γ ⊢[PRAAx] lt (length T + j) (length (append T T')) :=
  lt_congr (.eqRefl _) (append_length T T').eqSymm (add_lt_left (length T) hj)

theorem append_point (d : PR 3) (S S' T T' p i : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length T)) (hT' : Γ ⊢[PRAAx] le one (length T'))
    (hi : Γ ⊢[PRAAx] lt i (length (append S S'))) :
    Γ ⊢[PRAAx] le (distanceTo d (entry (append S S') i) (append T T') p)
      (maximum (hausdorff d S T p) (hausdorff d S' T' p)) := by
  have total : Γ ⊢[PRAAx] lt i (length S + length S') :=
    lt_congr (.eqRefl _) (append_length S S') hi
  refine .orE (lt_or_le i (length S)) ?_ ?_
  · let Δ := lt i (length S) :: Γ
    let j := nearest d (entry S i) T p
    have jRange : Δ ⊢[PRAAx] lt j (length T) := .andE₁ (nearest_spec d _ _ _ hT.wk)
    have sourceEq : Δ ⊢[PRAAx] entry (append S S') i ≐ entry S i := append_left Prf.hyp0
    have targetEq : Δ ⊢[PRAAx] entry (append T T') j ≐ entry T j := append_left jRange
    have bound : Δ ⊢[PRAAx]
        le (distance d (entry (append S S') i) (entry (append T T') j) p)
          (maximum (hausdorff d S T p) (hausdorff d S' T' p)) :=
      le_congr (congrAp3 d sourceEq targetEq (.eqRefl _)).eqSymm (.eqRefl _)
        (le_trans (nearest_error d S T p i hT.wk Prf.hyp0)
          (le_trans (maximum_left _ _) (maximum_left _ _)))
    exact le_trans (distanceTo_le d _ _ _ j (left_range T T' j jRange)) bound
  · let Δ := le (length S) i :: Γ
    let k := monus i (length S)
    let j := nearest d (entry S' k) T' p
    have kRange : Δ ⊢[PRAAx] lt k (length S') := suffix_range Prf.hyp0 total.wk
    have jRange : Δ ⊢[PRAAx] lt j (length T') := .andE₁ (nearest_spec d _ _ _ hT'.wk)
    have sourceEq : Δ ⊢[PRAAx] entry (append S S') i ≐ entry S' k :=
      append_right_at Prf.hyp0 total.wk
    have targetEq : Δ ⊢[PRAAx] entry (append T T') (length T + j) ≐ entry T' j := append_right jRange
    have bound : Δ ⊢[PRAAx]
        le (distance d (entry (append S S') i) (entry (append T T') (length T + j)) p)
          (maximum (hausdorff d S T p) (hausdorff d S' T' p)) :=
      le_congr (congrAp3 d sourceEq targetEq (.eqRefl _)).eqSymm (.eqRefl _)
        (le_trans (nearest_error d S' T' p k hT'.wk kRange)
          (le_trans (maximum_left _ _) (maximum_right _ _)))
    exact le_trans (distanceTo_le d _ _ _ (length T + j) (right_range T T' j jRange)) bound

theorem directed_append (d : PR 3) (S S' T T' p : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length T)) (hT' : Γ ⊢[PRAAx] le one (length T')) :
    Γ ⊢[PRAAx] le (directed d (append S S') (append T T') p)
      (maximum (hausdorff d S T p) (hausdorff d S' T' p)) := by
  apply directed_bound
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (append S S'))) :: Γ.map Fm.shift
  have positiveT : Δ ⊢[PRAAx] le one (length (Syn.shift T)) := by
    simpa only [Fm.shift, subst_le, SequenceComposition.subst_length, Syn.shift,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using hT.shift.wk
  have positiveT' : Δ ⊢[PRAAx] le one (length (Syn.shift T')) := by
    simpa only [Fm.shift, subst_le, SequenceComposition.subst_length, Syn.shift,
      ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using hT'.shift.wk
  have range : Δ ⊢[PRAAx] lt (var 0) (length (append (Syn.shift S) (Syn.shift S'))) := by
    simpa only [Δ, Syn.shift, SequenceComposition.subst_append] using
      (Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift)
        (φ := lt (var 0) (length (Syn.shift (append S S')))))
  have result := append_point d (Syn.shift S) (Syn.shift S') (Syn.shift T) (Syn.shift T')
    (Syn.shift p) (var 0) positiveT positiveT' range
  simpa only [Δ, Syn.shift, SequenceComposition.subst_append, subst_hausdorff,
    DemandClosure.subst_maximum] using result

theorem hausdorff_append (d : PR 3) (S S' T T' p : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hS' : Γ ⊢[PRAAx] le one (length S'))
    (hT : Γ ⊢[PRAAx] le one (length T)) (hT' : Γ ⊢[PRAAx] le one (length T')) :
    Γ ⊢[PRAAx] le (hausdorff d (append S S') (append T T') p)
      (maximum (hausdorff d S T p) (hausdorff d S' T' p)) := by
  apply maximum_le (directed_append d S S' T T' p hT hT')
  have reverse := directed_append d T T' S S' p hS hS'
  have eq : Γ ⊢[PRAAx]
      maximum (hausdorff d T S p) (hausdorff d T' S' p) ≐
        maximum (hausdorff d S T p) (hausdorff d S' T' p) :=
    congrAdd (hausdorff_symm d T S p)
      (congrMonus (hausdorff_symm d T' S' p) (hausdorff_symm d T S p))
  exact le_congr (.eqRefl _) eq reverse

theorem concatenation_closed (d : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶
        le one (length (var 2)) ⟶ le one (length (var 3)) ⟶
          le (hausdorff d (append (var 0) (var 1)) (append (var 2) (var 3)) (var 4))
            (maximum (hausdorff d (var 0) (var 2) (var 4))
              (hausdorff d (var 1) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (hausdorff_append d _ _ _ _ _
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))

#print axioms suffix_range
#print axioms append_point
#print axioms directed_append
#print axioms hausdorff_append
#print axioms concatenation_closed

end LeanProofs.IPRA.Foundations.FiniteHausdorffConcat
