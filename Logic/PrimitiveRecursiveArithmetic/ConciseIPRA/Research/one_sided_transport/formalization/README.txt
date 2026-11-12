PROPOSED LEAN EXTENSION -- NOT COMPILED
====================================

NativeOneSided.lean is written for the existing ConciseIPRA library at:

    ProveIt commit 8eb71c1e570e07ef45ead686628e77f18ef34798
    lean-toolchain: leanprover/lean4:v4.32.0

No Lean executable is available in the delivery environment. The new file
has NOT been compiled; it is a proposed formalization, not a verified Lean
artifact. The written proof does not depend on its successful elaboration.

To check it, use a separate checkout or worktree of the pinned repository.
Place the module at:

    Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeOneSided.lean

Then, from the repository root with its existing Lake dependencies available:

    lake build +ConciseIPRA.NativeOneSided

The accompanying reference/lean directory contains all 35 exact modules
from the pinned ConciseIPRA tree for inspection; it is not a standalone
replacement for the repository's Lake project and Mathlib dependencies.

Main proposed results:

    CPrf.trEqRestricted          Two X applications simulate old transport.
    CPrf.eqRefl / eqSymm         Zero computation and X suffice.
    CPrf.zeroJoin / eqTrans      Recovery at syntactic zero.
    CPrf.eqCongr / trEq          Unrestricted numerical equality reasoning.
    cprf_iff_nprf                Exact equivalence with the native core.
    cprf_iff_mprf                Exact equivalence with existing seven rules.
    oneSided_iff_pra             Forward faithfulness.
    pra_iff_oneSided             Reverse faithfulness.
    oneSided_roundTrip           Native composite.
    pra_oneSided_roundTrip       iPRA composite.
    oneSided_inconsistent_iff    Equiconsistency.

The imports reuse the established NativeMinimal and NativeBiInterpretation
developments. No new logical or nonlogical axiom is postulated by the file.
