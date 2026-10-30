import BusyBeaver.ZFC.FiniteZipper

/-!
Sequential execution and symbolic scans for the existing finite zipper.
All execution theorems transfer to `BusyBeaver.Core.runFrom` through ZipRep.
The tape coordinates and every exterior cell remain part of that relation.
-/

namespace SetTheory.BusyBeaver.ZFC.ZipperRuns

open FiniteZipper

def zAt {n : Nat} (q : Fin n) (head : Int) (left right : List Bool) : ZipConfig n :=
  { state := some q, head := head, left := left, right := right }

/-- The head is one cell left of the boundary between the two lists. -/
def leftAt {n : Nat} (q : Fin n) (boundary : Int)
    (left right : List Bool) : ZipConfig n :=
  { state := some q, head := boundary - 1,
    left := left.tail, right := left.getD 0 false :: right }

def zipRun {n : Nat} (M : Machine n) (z : ZipConfig n) : Nat → ZipConfig n
  | 0 => z
  | k + 1 => zipStep M (zipRun M z k)

theorem zipRun_add {n : Nat} (M : Machine n) (z : ZipConfig n) (i j : Nat) :
    zipRun M z (i + j) = zipRun M (zipRun M z i) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change zipStep M (zipRun M z (i + j)) = zipStep M (zipRun M (zipRun M z i) j)
    rw [ih]

theorem zipRun_first {n : Nat} (M : Machine n) (z : ZipConfig n) (k : Nat) :
    zipRun M z (k + 1) = zipRun M (zipStep M z) k := by
  simpa only [Nat.add_comm, zipRun] using zipRun_add M z 1 k

/-- Sequential finite execution is sound for the already existing Core machine. -/
theorem zipRun_sound {n : Nat} (M : Machine n) (k : Nat)
    {c : Config n} {z : ZipConfig n} (h : ZipRep c z) :
    ZipRep (M.runFrom c k) (zipRun M z k) := by
  induction k with
  | zero => exact h
  | succ k ih => exact zipStep_sound M ih

theorem step_right {n : Nat} (M : Machine n) (q q' : Fin n)
    (bit written : Bool) (h : Int) (l r : List Bool)
    (ht : M.transition q bit = ⟨written, .right, some q'⟩) :
    zipStep M (zAt q h l (bit :: r)) = zAt q' (h + 1) (written :: l) r := by
  simp [zipStep, zAt, ht, zipWrite, zipRight]

theorem step_left {n : Nat} (M : Machine n) (q q' : Fin n)
    (bit written : Bool) (h : Int) (l r : List Bool)
    (ht : M.transition q bit = ⟨written, .left, some q'⟩) :
    zipStep M (zAt q h l (bit :: r)) = leftAt q' h l (written :: r) := by
  simp [zipStep, zAt, leftAt, ht, zipWrite, zipLeft]

theorem leftAt_cons {n : Nat} (q : Fin n) (h : Int)
    (bit : Bool) (l r : List Bool) :
    leftAt q h (bit :: l) r = zAt q (h - 1) l (bit :: r) := rfl

/-- Exact execution of a preserving right scan, for every finite length. -/
theorem scan_right {n : Nat} (M : Machine n) (q : Fin n) (bit : Bool)
    (ht : M.transition q bit = ⟨bit, .right, some q⟩)
    (k : Nat) (h : Int) (l r : List Bool) :
    zipRun M (zAt q h l (List.replicate k bit ++ r)) k =
      zAt q (h + (k : Int)) (List.replicate k bit ++ l) r := by
  induction k generalizing h l with
  | zero => simp [zipRun]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, zipRun_first,
      step_right M q q bit bit h l _ ht, ih]
    have eh : h + 1 + (k : Int) = h + ((k + 1 : Nat) : Int) := by omega
    rw [eh]
    have el : List.replicate k bit ++ bit :: l = (bit :: List.replicate k bit) ++ l := by
      calc
        _ = (List.replicate k bit ++ [bit]) ++ l := (List.append_assoc _ _ _).symm
        _ = _ := by rw [← List.replicate_succ', List.replicate_succ]
    rw [el]

/-- Exact execution of a preserving left scan, in the boundary-left view. -/
theorem scan_left {n : Nat} (M : Machine n) (q : Fin n) (bit : Bool)
    (ht : M.transition q bit = ⟨bit, .left, some q⟩)
    (k : Nat) (h : Int) (l r : List Bool) :
    zipRun M (leftAt q h (List.replicate k bit ++ l) r) k =
      leftAt q (h - (k : Int)) l (List.replicate k bit ++ r) := by
  induction k generalizing h r with
  | zero => simp [zipRun]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, leftAt_cons, zipRun_first,
      step_left M q q bit bit (h - 1) _ r ht, ih]
    have eh : h - 1 - (k : Int) = h - ((k + 1 : Nat) : Int) := by omega
    rw [eh]
    have er : List.replicate k bit ++ bit :: r = (bit :: List.replicate k bit) ++ r := by
      calc
        _ = (List.replicate k bit ++ [bit]) ++ r := (List.append_assoc _ _ _).symm
        _ = _ := by rw [← List.replicate_succ', List.replicate_succ]
    rw [er]

#print axioms zipRun_sound
#print axioms scan_right
#print axioms scan_left

end SetTheory.BusyBeaver.ZFC.ZipperRuns
