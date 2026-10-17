import BusyBeaver.ZFC.Bisim254
import BusyBeaver.ZFC.ZFNative
import BusyBeaver.ZFC.WFTheory

/-!
The register-program endpoint for the literal decoder tree.

`Prog254.program` is the 6459-row register program that the public machine
table decodes (Codex lane), started from its public initial configuration.
Composing L4 (`Bisim254.literal_halts_iff`), the Codex lane's native-theory
comparison (`NativeTheory254.c254_refutation_iff`) and `ZFNative`:

* the literal program halts iff the native theory is refutable;
* if it halts, ZF and ZFC are refutable; so **Con(ZFC) implies that it never
  halts**.

The converse direction (a refutation of ZFC makes the program halt) needs the
Regularity and Choice transports from ZFC down to the native theory, which
the Codex lane is pursuing; the binary machine needs the TM layer
(literal table ↔ path semantics of `Prog254`).
-/

namespace SetTheory.BusyBeaver.ZFC.Endpoint254

open NativeTheory254

/-- The literal program halts iff the native theory is refutable. -/
theorem literal_halts_iff_native_refutation :
    RegisterPath.Halts Prog254.program Prog254.initial ↔ BProv NativeAx [] Form.fBot :=
  Bisim254.literal_halts_iff.trans c254_refutation_iff

/-- Halting of the literal program refutes ZF. -/
theorem zf_refutation_of_literal_halting (h : RegisterPath.Halts Prog254.program Prog254.initial) :
    BProv ZFax_s [] Form.fBot :=
  ZFNative.zf_refutation_of_native (literal_halts_iff_native_refutation.mp h)

/-- Halting of the literal program refutes ZFC. -/
theorem zfc_refutation_of_literal_halting (h : RegisterPath.Halts Prog254.program Prog254.initial) :
    BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  BProv_theory_mono (fun _ hb => Or.inl hb) (zf_refutation_of_literal_halting h)

/-- **Con(ZFC) implies that the literal register program never halts.** -/
theorem literal_nonhalting_of_zfc_consistent
    (hCon : ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot) :
    ¬ RegisterPath.Halts Prog254.program Prog254.initial :=
  fun h => hCon (zfc_refutation_of_literal_halting h)

/-- **The literal program halts iff ZF is refutable** (Foundation and Power,
no Choice): L4 with the Codex lane’s `WFTheory.c254_refutation_iff_zf`. -/
theorem literal_halts_iff_zf_refutation :
    RegisterPath.Halts Prog254.program Prog254.initial ↔ BProv ZFax_s [] Form.fBot :=
  Bisim254.literal_halts_iff.trans WFTheory.c254_refutation_iff_zf

/-- **Non-halting of the literal program is Con(ZF).** -/
theorem literal_nonhalting_iff_zf_consistent :
    ¬ RegisterPath.Halts Prog254.program Prog254.initial ↔ ¬ BProv ZFax_s [] Form.fBot :=
  not_congr literal_halts_iff_zf_refutation

end SetTheory.BusyBeaver.ZFC.Endpoint254
