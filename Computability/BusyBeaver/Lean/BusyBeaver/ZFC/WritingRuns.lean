import BusyBeaver.ZFC.ZipperRuns

/-!
Exact scans which can overwrite a repeated tape bit.

These extend the interface of ZipperRuns without assuming that the bit read
is also the bit written. Each theorem retains the absolute head coordinate,
both finite tape contexts, and the whole-tape interpretation through ZipRep.
The transition premise is for the actual machine supplied by the caller.
-/

namespace SetTheory.BusyBeaver.ZFC.WritingRuns

open FiniteZipper ZipperRuns

/-- A rightward self-loop writes every cell of the supplied finite run. -/
theorem scan_right_write {n : Nat} (M : Machine n) (q : Fin n)
    (read written : Bool)
    (ht : M.transition q read = ⟨written, .right, some q⟩)
    (k : Nat) (h : Int) (l r : List Bool) :
    zipRun M (zAt q h l (List.replicate k read ++ r)) k =
      zAt q (h + (k : Int)) (List.replicate k written ++ l) r := by
  induction k generalizing h l with
  | zero => simp [zipRun]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, zipRun_first,
      step_right M q q read written h l _ ht, ih]
    have eh : h + 1 + (k : Int) = h + ((k + 1 : Nat) : Int) := by omega
    rw [eh]
    have el : List.replicate k written ++ written :: l =
        (written :: List.replicate k written) ++ l := by
      calc
        _ = (List.replicate k written ++ [written]) ++ l :=
          (List.append_assoc _ _ _).symm
        _ = _ := by rw [← List.replicate_succ', List.replicate_succ]
    rw [el]
    simp only [List.replicate_succ, List.cons_append]

/-- The leftward form, with the head one cell left of the list boundary. -/
theorem scan_left_write {n : Nat} (M : Machine n) (q : Fin n)
    (read written : Bool)
    (ht : M.transition q read = ⟨written, .left, some q⟩)
    (k : Nat) (h : Int) (l r : List Bool) :
    zipRun M (leftAt q h (List.replicate k read ++ l) r) k =
      leftAt q (h - (k : Int)) l (List.replicate k written ++ r) := by
  induction k generalizing h r with
  | zero => simp [zipRun]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, leftAt_cons, zipRun_first,
      step_left M q q read written (h - 1) _ r ht, ih]
    have eh : h - 1 - (k : Int) = h - ((k + 1 : Nat) : Int) := by omega
    rw [eh]
    have er : List.replicate k written ++ written :: r =
        (written :: List.replicate k written) ++ r := by
      calc
        _ = (List.replicate k written ++ [written]) ++ r :=
          (List.append_assoc _ _ _).symm
        _ = _ := by rw [← List.replicate_succ', List.replicate_succ]
    rw [er]
    simp only [List.replicate_succ, List.cons_append]

theorem scan_right_write_core {n : Nat} (M : Machine n) (q : Fin n)
    (read written : Bool)
    (ht : M.transition q read = ⟨written, .right, some q⟩)
    (k : Nat) (h : Int) (l r : List Bool) {c : Config n}
    (hc : ZipRep c (zAt q h l (List.replicate k read ++ r))) :
    ZipRep (M.runFrom c k)
      (zAt q (h + (k : Int)) (List.replicate k written ++ l) r) := by
  have hs := zipRun_sound M k hc
  rw [scan_right_write M q read written ht] at hs
  exact hs

theorem scan_left_write_core {n : Nat} (M : Machine n) (q : Fin n)
    (read written : Bool)
    (ht : M.transition q read = ⟨written, .left, some q⟩)
    (k : Nat) (h : Int) (l r : List Bool) {c : Config n}
    (hc : ZipRep c (leftAt q h (List.replicate k read ++ l) r)) :
    ZipRep (M.runFrom c k)
      (leftAt q (h - (k : Int)) l (List.replicate k written ++ r)) := by
  have hs := zipRun_sound M k hc
  rw [scan_left_write M q read written ht] at hs
  exact hs

end SetTheory.BusyBeaver.ZFC.WritingRuns
