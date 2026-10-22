import BusyBeaver.ZFC.QuotientZF0
import BusyBeaver.ZFC.Enum254

/-! The abstract 254 enumerator's consequences of `QuotientZF0.c254_of_zf0_refutation`, kept
apart so that `QuotientZF0`'s clients (the K215 endpoint among them) do not import `Enum254`.
The two theorems are moved verbatim and keep their namespace and names. -/

namespace SetTheory.BusyBeaver.ZFC.QuotientZF0

/-- This is the abstract six-register enumerator, not Prog254 or the binary TM. -/
theorem enum_halts_of_zf0_refutation (hf : BProv PSCCalibration.ZF0Ax [] .fBot) :
    Enum254.Halts :=
  Enum254.complete (c254_of_zf0_refutation hf)

/-- The corresponding one-way consistency statement, at the abstract level. -/
theorem zf0_consistent_of_enum_nonhalting (h : ¬ Enum254.Halts) :
    ¬ BProv PSCCalibration.ZF0Ax [] .fBot :=
  fun hf => h (enum_halts_of_zf0_refutation hf)

end SetTheory.BusyBeaver.ZFC.QuotientZF0
