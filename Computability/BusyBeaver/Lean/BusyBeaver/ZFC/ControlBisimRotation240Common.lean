import BusyBeaver.ZFC.DagControl254

set_option autoImplicit false

/-!
Shared literal-table views and a finite certificate concatenation lemma.
The four public views retain the original ControlBisimRotation240 definitions.
This module evaluates no concrete certificate interval. New proofs use defaults.
-/

namespace SetTheory.BusyBeaver.ZFC.ControlBisimRotation240

open ArithmeticControlBisim ArithmeticControlTable

/-- The row table of the Rotation240 control interpreter. -/
abbrev tableR : List Row := PackedTables.table BisimCertRotation240.tableR BisimCertRotation240.countR

abbrev rowsLitR (c : Nat) : Option Row :=
  PackedTables.rowsOf BisimCertRotation240.tableR BisimCertRotation240.countR c

abbrev cert (i : Nat) : Option Entry :=
  PackedTables.certOf BisimCertRotation240.certPacked BisimCertRotation240.size i

abbrev chunk (start count : Nat) : Bool :=
  checkFrom DagControl254.rowsLit rowsLitR cert BisimCertRotation240.fuel
    BisimCertRotation240.size start count

end SetTheory.BusyBeaver.ZFC.ControlBisimRotation240

namespace SetTheory.BusyBeaver.ZFC.ControlBisimRotation240Split

open ArithmeticControlBisim ControlBisimRotation240

/-- Two adjacent passing finite intervals imply their concatenation passes. -/
theorem checkFrom_join (rowsA rowsB : Nat → Option Row) (cert : Nat → Option Entry)
    (fuel bound m : Nat) : ∀ i n,
    checkFrom rowsA rowsB cert fuel bound i m = true →
    checkFrom rowsA rowsB cert fuel bound (i + m) n = true →
    checkFrom rowsA rowsB cert fuel bound i (m + n) = true := by
  induction m with
  | zero =>
    intro i n _ hright
    simpa only [Nat.zero_add, Nat.add_zero] using hright
  | succ m ih =>
    intro i n hleft hright
    change (entryOK rowsA rowsB cert fuel bound i &&
      checkFrom rowsA rowsB cert fuel bound (i + 1) m) = true at hleft
    rw [Bool.and_eq_true] at hleft
    have hright' : checkFrom rowsA rowsB cert fuel bound ((i + 1) + m) n = true := by
      rw [show (i + 1) + m = i + (m + 1) by omega]
      exact hright
    rw [Nat.succ_add, checkFrom, Bool.and_eq_true]
    exact ⟨hleft.1, ih (i + 1) n hleft.2 hright'⟩

/-- Concatenate intervals of the unchanged concrete certificate predicate. -/
theorem chunk_join (i m n : Nat) (hleft : chunk i m = true)
    (hright : chunk (i + m) n = true) : chunk i (m + n) = true :=
  checkFrom_join DagControl254.rowsLit rowsLitR cert BisimCertRotation240.fuel
    BisimCertRotation240.size m i n hleft hright

end SetTheory.BusyBeaver.ZFC.ControlBisimRotation240Split
