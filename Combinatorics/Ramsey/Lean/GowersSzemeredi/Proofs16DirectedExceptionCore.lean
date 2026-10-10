import GowersSzemeredi.Proofs16ProgressionImagePurification

/-! Prune a directed exceptional pair set on any prescribed vertex domain.
Both incoming and outgoing degrees are controlled, and the lost vertex
mass is charged only to the original exceptional pairs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def exceptionalPairOutDegree {V : Type*} [DecidableEq V] (E : Finset (V × V)) (x : V) : Nat :=
  (E.filter fun p => p.1=x).card

def exceptionalPairInDegree {V : Type*} [DecidableEq V] (E : Finset (V × V)) (x : V) : Nat :=
  (E.filter fun p => p.2=x).card

def directedExceptionCore {V : Type*} [DecidableEq V]
    (D : Finset V) (E : Finset (V × V)) (t : Nat) : Finset V :=
  D.filter fun x => exceptionalPairOutDegree E x ≤ t ∧ exceptionalPairInDegree E x ≤ t

/-- Threshold exceedances are bounded by the total nonnegative weight. -/
theorem threshold_exceptions_card_le_sum {V : Type*} [DecidableEq V]
    (D : Finset V) (f : V → Nat) (t : Nat) :
    (t+1)*(D.filter fun x => t < f x).card ≤ ∑ x ∈ D, f x := by
  let B := D.filter fun x => t < f x
  calc (t+1)*B.card = ∑ _x ∈ B, (t+1) := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ B, f x := Finset.sum_le_sum fun x hx =>
      Nat.succ_le_of_lt (Finset.mem_filter.mp hx).2
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)

/-- Pruning controls both directed incidences while losing at most
`2*|E|/(t+1)` vertices of the prescribed domain. -/
theorem directed_exception_core_loss {V : Type*} [DecidableEq V]
    (D : Finset V) (E : Finset (V × V)) (t : Nat) :
    (t+1)*(D \ directedExceptionCore D E t).card ≤ 2*E.card := by
  let O := D.filter fun x => t < exceptionalPairOutDegree E x
  let I := D.filter fun x => t < exceptionalPairInDegree E x
  have hsub : D \ directedExceptionCore D E t ⊆ O ∪ I := by
    intro x hx
    obtain ⟨hxD, hxnot⟩ := Finset.mem_sdiff.mp hx
    have hn : ¬(exceptionalPairOutDegree E x ≤ t ∧ exceptionalPairInDegree E x ≤ t) := by
      intro h
      exact hxnot (Finset.mem_filter.mpr ⟨hxD,h⟩)
    by_cases ho : exceptionalPairOutDegree E x ≤ t
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxD, by omega⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxD, by omega⟩)
  have hout : ∑ x ∈ D, exceptionalPairOutDegree E x ≤ E.card := by
    dsimp only [exceptionalPairOutDegree]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_filter_le _ _
  have hin : ∑ x ∈ D, exceptionalPairInDegree E x ≤ E.card := by
    dsimp only [exceptionalPairInDegree]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    exact Finset.card_filter_le _ _
  have ho : (t+1)*O.card ≤ E.card := (threshold_exceptions_card_le_sum D (exceptionalPairOutDegree E) t).trans hout
  have hi : (t+1)*I.card ≤ E.card := (threshold_exceptions_card_le_sum D (exceptionalPairInDegree E) t).trans hin
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le O I)
  calc (t+1)*(D \ directedExceptionCore D E t).card ≤ (t+1)*(O.card+I.card) :=
      Nat.mul_le_mul_left _ hc
    _ = (t+1)*O.card+(t+1)*I.card := Nat.mul_add _ _ _
    _ ≤ 2*E.card := by omega

/-- The real mass form retains the exact natural threshold denominator. -/
theorem directed_exception_core_mass {V : Type*} [DecidableEq V]
    (D : Finset V) (E : Finset (V × V)) (t : Nat) :
    (D.card : Real)-2*(E.card : Real)/(t+1) ≤ (directedExceptionCore D E t).card := by
  have hloss := directed_exception_core_loss D E t
  have hR : ((t : Real)+1)*(D \ directedExceptionCore D E t).card ≤ 2*(E.card : Real) := by
    exact_mod_cast hloss
  have hbound : ((D \ directedExceptionCore D E t).card : Real) ≤ 2*(E.card : Real)/(t+1) := by
    apply (le_div_iff₀ (by positivity : 0 < (t : Real)+1)).mpr
    simpa only [mul_comm] using hR
  have hpartition : ((D \ directedExceptionCore D E t).card : Real)+
      (directedExceptionCore D E t).card = D.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  linarith

end LeanProofs.GowersSzemeredi
