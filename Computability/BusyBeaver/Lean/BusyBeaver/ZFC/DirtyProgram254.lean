import BusyBeaver.ZFC.DirtyRoot254
import BusyBeaver.ZFC.RMEquiv254
import BusyBeaver.ZFC.NativeTheory254

/-!
Arbitrary dirty root starts for the exact 219-node structured program.

The absorption and safe-start arguments are attributed to intake 153,
source 35 (arrival 4e720ccbbfaa836b95be3b2f3f268a737b48c6d1; preserved
placement 6135ffef4b). This module composes those ported proofs with the
current clean-root, path-semantics and actual native-theory interfaces.

The six nonformula fields may be arbitrary. Soundness still requires the
exact formula invariant, and `L2.enc` still sets registers at indices >= 9
to zero. The path program here is the 219-node `RMEquiv254.pathDag254`.
No binary frame, blank initialization, full ZFC calibration or proof-code
internalization is inferred by these theorems.
-/

namespace SetTheory.BusyBeaver.ZFC.DirtyProgram254

open RMDag Dag254 Code254 L2

/-- Exactly the existing top/cache/stack invariant; no numerical-control
field is restricted. -/
abbrev Safe (st : AS) : Prop := Enum254.Inv (DirtyRoot254.enumOf st)

theorem safe_iff (st : AS) :
    Safe st ↔ C254 st.tw ∧ C254 st.p2 ∧ Enum254.Good st.ws := Iff.rfl

/-- The encoded logical register tail is zero, independently of all nine fields. -/
theorem enc_tail (st : AS) (i : Nat) : L2.enc st (i + 9) = 0 := rfl

theorem toAS_enumOf_of_clean (st : AS)
    (ha : st.ac = 0) (hx : st.s1 = 0) (hy : st.s2 = 0) :
    L2.toAS (DirtyRoot254.enumOf st) = st := by
  cases st
  simp_all [L2.toAS, DirtyRoot254.enumOf]

theorem virtual_toAS (st : AS) :
    L2.toAS (DirtyRoot254.enumOf (DirtyRoot254.virtual st)) =
      DirtyRoot254.virtual st := by
  obtain ⟨ha, hx, hy⟩ := DirtyRoot254.virtual_clean st
  exact toAS_enumOf_of_clean _ ha hx hy

/-- Exact comparison to the absorbed enumerator, with no soundness invariant. -/
theorem iter_iff_virtual_enum (st : AS) :
    IterHalts dag254 (L2.enc st) ↔
      EnumSafeStart254.HaltsFrom (DirtyRoot254.enumOf (DirtyRoot254.virtual st)) := by
  refine (DirtyRoot254.iter_equiv st).trans ?_
  simpa only [virtual_toAS, EnumSafeStart254.HaltsFrom] using
    (L2.iter_iff (DirtyRoot254.enumOf (DirtyRoot254.virtual st)))

/-- Numerical inconsistency makes every encoded dirty root start halt.
This direction needs no assumptions about the initial formula fields. -/
theorem complete_from (st : AS) (h : C254 F) :
    IterHalts dag254 (L2.enc st) :=
  (iter_iff_virtual_enum st).mpr (EnumSafeStart254.complete_from _ h)

/-- Both directions for every encoded root with safe formula data. -/
theorem iter_halts_iff (st : AS) (hs : Safe st) :
    IterHalts dag254 (L2.enc st) ↔ C254 F :=
  (iter_iff_virtual_enum st).trans (DirtyRoot254.virtual_enum_iff st hs)

/-- The same contract in the path semantics of the exact 219-node DAG. -/
theorem path_halts_iff (st : AS) (hs : Safe st) :
    RegisterPath.Halts RMEquiv254.pathDag254 ⟨[], L2.enc st⟩ ↔ C254 F :=
  (RMEquiv254.path_halts_iff_iter _).trans (iter_halts_iff st hs)

/-- Refutation of the exact sealed native CP/all-Form-GIC/IR theory. -/
theorem iter_halts_iff_native_refutation (st : AS) (hs : Safe st) :
    IterHalts dag254 (L2.enc st) ↔
      BProv NativeTheory254.NativeAx [] Form.fBot :=
  (iter_halts_iff st hs).trans NativeTheory254.c254_refutation_iff

theorem path_halts_iff_native_refutation (st : AS) (hs : Safe st) :
    RegisterPath.Halts RMEquiv254.pathDag254 ⟨[], L2.enc st⟩ ↔
      BProv NativeTheory254.NativeAx [] Form.fBot :=
  (path_halts_iff st hs).trans NativeTheory254.c254_refutation_iff

theorem native_consistency_iff_nonhalting (st : AS) (hs : Safe st) :
    (¬ BProv NativeTheory254.NativeAx [] Form.fBot) ↔
      ¬ IterHalts dag254 (L2.enc st) :=
  not_congr (iter_halts_iff_native_refutation st hs).symm

/-- All six nonformula fields are quantified explicitly. Only the top,
stack and retained formula are fixed to their known safe zero codes. -/
theorem six_nonformula_iff (N A D X Y L : Nat) :
    IterHalts dag254 (L2.enc ⟨N, 0, 0, A, D, 0, X, Y, L⟩) ↔
      BProv NativeTheory254.NativeAx [] Form.fBot :=
  iter_halts_iff_native_refutation _
    ⟨C254.truth, C254.truth, Enum254.good_zero⟩

theorem six_nonformula_path_iff (N A D X Y L : Nat) :
    RegisterPath.Halts RMEquiv254.pathDag254
      ⟨[], L2.enc ⟨N, 0, 0, A, D, 0, X, Y, L⟩⟩ ↔
      BProv NativeTheory254.NativeAx [] Form.fBot :=
  path_halts_iff_native_refutation _
    ⟨C254.truth, C254.truth, Enum254.good_zero⟩

end SetTheory.BusyBeaver.ZFC.DirtyProgram254
