# ROOT review: actual Home execution on internal 215 tapes

Accepted on 27 October 2026. ROOT read the complete final 234-line proof,
65-line Checks, author receipt and independent executed driver, then replayed
the unchanged pair in a fresh private overlay. Main and Checks passed in
4.619 and 2.375 seconds. Both objects, both full logs and all 14 axiom
reports match the author run. The main log is empty; the reports use only
`propext`, `Classical.choice` and `Quot.sound`.

The proof works in every arithmetic model of IΣ1, with arbitrary internal
gap, register values, spare count, numeric tape tails and execution clocks.
The finite symbolic syntax and checker fuel remain standard finite syntax.
Kernel checks establish the fifteen scanner rows, three boundary rows and
actual HomeReady certificate. The semantic boundary theorem independently
composes all eighteen actual steps and proves
`runFrom 18 (leftFrame 2 0 (2*R+1)) = frameSparse 84 1 R` for arbitrary R.

The scanBound invariant retains a bounded actual zero counter and the exact
reversed numeric fold. A true run may have internal length zero, including
at gap zero; the zero branch preserves the counter. Positive true runs
reset it. False runs have zero affine coefficient and fewer than eight
successive zeros. Boxes are rejected by the scanner. Exterior blank strips
vanish only at tail zero; the stopping marker must be a literal true bit.

`home_actual` supplies a genuine positive execution with no positive-spare
or branch premise. The actual HomeReady stepper uses this proof on success
and accepted symbolic execution on fallback, retaining its required positive
spare count and BranchValid premise. The executor preserves the moved flag:
positive execution follows from an initially false flag, while an initially
true flag guarantees ordinary reachability. Exact target matching is proved.
Focused clients cover both flags, zero gaps, empty true runs, right register
boxes, exterior zeros and all boundary steps.

The exact approved profile has 153 cached modules, 95 Foundation modules,
438 local artifacts, 41 boundary primaries plus 123 companions and 602 first
providers, with zero prerequisite refreshes. Both new inputs were preserved
before the first compiler invocation. Commands use M6000/j1/async=false,
one Lean thread, package-only fallback and a 512MiB reserve. The accepted
current KZip object remains selected; the documented historical alternate
has identical source but unequal object bytes. No equality of those objects
or new dependency compilation is claimed.

All four author attempts, six compiler invocations and eight input snapshots
remain authenticated. The independent driver verifies the 37-file author
manifest and exact source DAG/providers; the ROOT freeze reauthenticates the
selected inputs and final pairs. The [ROOT packet](arithmetic-home215-root-replay.json)
and [manifest](arithmetic-home215-root-replay/FILES.json) pin the independent
driver, inputs, source snapshots, logs and timings. The
[author packet](arithmetic-home215-replay.json) retains the development history.

Canonical accepted provider: `/tmp/home215-root-gwo_lm6e/lib`.
This result does not yet establish all site contracts, canonical reentry,
physical/control calibration or the whole control/tape equivalence. Source
ZFC interpretation and the final polynomial/PA/HA theorem remain open.
