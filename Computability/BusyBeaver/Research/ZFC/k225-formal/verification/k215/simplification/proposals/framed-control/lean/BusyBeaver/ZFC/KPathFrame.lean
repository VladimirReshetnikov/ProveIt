import BusyBeaver.ZFC.RegisterPath

/-!
Prefix preservation for the maintained K-family source path operations.
The hypotheses ensure that stripping and the carry stop in the explicit suffix.
No claim about Turing-machine execution is hidden in these list lemmas.
-/
namespace SetTheory.BusyBeaver.ZFC.KPathFrame
open RegisterPath

theorem stripRev_append (b : Bool) (S F : List Bool) (k : Nat)
    (h : k ≤ S.count b) :
    stripRev b k (S ++ F) = stripRev b k S ++ F := by
  induction S generalizing k with
  | nil =>
      have hk : k = 0 := by simpa using h
      subst k
      simp [stripRev]
  | cons x S ih =>
      cases k with
      | zero => rfl
      | succ k =>
          by_cases hx : x = b
          · subst x
            have hk : k ≤ S.count b := by simpa using h
            simpa [stripRev] using ih k hk
          · have hk : k + 1 ≤ S.count b := by simpa [List.count_cons, hx] using h
            simpa only [List.cons_append, stripRev, if_neg hx] using ih (k + 1) hk

theorem incRev_append (S F : List Bool) (h : false ∈ S) :
    incRev (S ++ F) = incRev S ++ F := by
  induction S with
  | nil => simp at h
  | cons x S ih =>
      cases x with
      | false => rfl
      | true =>
          have ht : false ∈ S := by simpa using h
          simpa only [List.cons_append, incRev] using congrArg (List.cons false) (ih ht)

theorem stripPath_append (b : Bool) (P S : List Bool) (k : Nat)
    (h : k ≤ S.count b) :
    stripPath b k (P ++ S) = P ++ stripPath b k S := by
  have hr : k ≤ S.reverse.count b := by simpa using h
  simp only [stripPath, List.reverse_append]
  rw [stripRev_append b S.reverse P.reverse k hr]
  simp only [List.reverse_append, List.reverse_reverse]

theorem incPath_append (P S : List Bool) (h : false ∈ S) :
    incPath (P ++ S) = P ++ incPath S := by
  have hr : false ∈ S.reverse := by simpa using h
  simp only [incPath, List.reverse_append]
  rw [incRev_append S.reverse P.reverse hr]
  simp only [List.reverse_append, List.reverse_reverse]

theorem continuePath_append (P S : List Bool) (k : Nat)
    (h : k ≤ S.count true) :
    continuePath k (P ++ S) = P ++ continuePath k S :=
  stripPath_append true P S k h

theorem breakPath_append (P S : List Bool) (k : Nat)
    (hstrip : k ≤ S.count false) (hcarry : false ∈ stripPath false k S) :
    breakPath k (P ++ S) = P ++ breakPath k S := by
  rw [breakPath, stripPath_append false P S k hstrip,
    incPath_append P (stripPath false k S) hcarry]
  rfl

theorem source_gap_rebase (n : Nat) {P S : List Bool}
    (hlen : (P ++ S).length ≤ 48) :
    n + (64 - (P ++ S).length) = (n + 48 - (P ++ S).length) + 16 := by
  omega

theorem target_gap_rebase (n : Nat) {P S E : List Bool}
    (hlen : (P ++ S).length ≤ 48) (hshort : E.length ≤ S.length) :
    (n + 48 - (P ++ S).length) + 16 + S.length - E.length =
      n + (64 - (P ++ E).length) := by
  simp only [List.length_append] at *
  omega

/-- Without the carry guard, a break can change the hidden prefix. -/
theorem carry_guard_necessary :
    breakPath 1 ([false] ++ [true, false]) ≠
      [false] ++ breakPath 1 [true, false] := by decide

/-- Without enough target bits in the suffix, stripping reads the prefix. -/
theorem strip_guard_necessary :
    continuePath 1 ([true] ++ [false]) ≠
      [true] ++ continuePath 1 [false] := by decide

#print axioms stripRev_append
#print axioms incRev_append
#print axioms stripPath_append
#print axioms incPath_append
#print axioms continuePath_append
#print axioms breakPath_append
#print axioms source_gap_rebase
#print axioms target_gap_rebase
#print axioms carry_guard_necessary
#print axioms strip_guard_necessary

end SetTheory.BusyBeaver.ZFC.KPathFrame
