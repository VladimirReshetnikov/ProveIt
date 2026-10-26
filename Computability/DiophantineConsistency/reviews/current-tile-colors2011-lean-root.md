# Matching actual tile colors and nonzero temporal displacement

Date: 2026-10-26. Author and complete source/check reviewer: ROOT.
This is an author receipt, not an independent peer review.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentTileColors2011.lean (104 lines) | c1f7fc6fda51795f182c0d14379206c781f8cdcae212e27ff5c0a9bede21b8f9 |
| CurrentTileColors2011Checks.lean (43 lines) | 2c3f698e2ddc61bf19f8c608f2cf2ebe64f85a3f2ab6644db225c0cffc9a1c7d |

Both complete sources were read before execution. The initial main run
needed explicit destructuring of the tile-bound conjunctions for omega
and a type annotation on the zero temporal base. Those elaboration changes
were read before replay. The final main and the first checks run both
passed with `lake env lean -M6000 -j1`, asynchronous elaboration disabled.
The main log is empty and all five axiom reports contain only the standard
axioms. The main object was generated from this final source and imported
by the checks. No full dependency or umbrella rebuild is claimed.

`facts_selected_labels` derives all four copied color blocks for an actual
selected index from the original decoded clause. `facts_horizontal_colors`
and `facts_temporal_colors` aggregate the complete physical copy equalities
and cancel the complements using the actual color bounds. The orientation
is East(current)=West(previous), South(current)=North(temporal). All count,
fractional phase, whole-field alignment, masks and labels are derived from
the same original Facts and functions. These local theorems accept the
two selected indices explicitly; global occupation is a separate theorem.

`facts_temporal_shift_nonzero` needs only Facts. If the original rank-based
shift divided by47 were zero in ZMod(N*2011), the actual Start index0 would
temporally match itself. Its South1 differs from its North435, so matching
is impossible. This excludes every multiple of the full word period,
including positive natural shifts, without assuming occupation anywhere
else or bounding the natural shift. The focused divisibility check makes
that stronger scope explicit; another check retains the abstract zero
shift allowed by alignment alone.

The global marked Wang word, machine semantics, converse/controller and
internal-ZFC proof remain open. The displayed decimal equation and its
metrics are unchanged.
