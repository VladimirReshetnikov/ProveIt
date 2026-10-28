# Independent ROOT acceptance: canonical215 control frame

Accepted on 27 October 2026 after complete review of the final 467-line main,
72-line Checks, author receipt, 139-line executed replay driver, frozen plan
and its source/provider inventory. The complete pair was compiled afresh in
`/tmp/control-frame215-root-90hncefu`, separately from the author's outputs.

## Result and scope

The canonical entry graph is fixed before the arithmetic model is chosen.
It retains the actual one-based compact control lookup, all nine physical
registers, complete spare/header encoding and arbitrary internal gap.
The physical permutation is applied once. Outgoing paths rebase to the next
actual consumed path, preserving the entire right suffix. The padding
calculation includes paths longer than the nominal left padding.

Actual source membership and all six accepted site execution contracts yield
`entry_step` and `entry_halt`. Step derives a new actual control, file,
positive clock and gap with positive tape execution; halt has the actual
terminal predicate `first(configuration) = 0`. The finite control index is
selected from a supported opcode, rather than supplied as an oracle. Gap
zero, the first physical register mapping and table boundary failures are
included in the checks.

This supplies local canonical transport. Whole iteration, the fixed initial
frame and boot composition remain for the next runtime theorem. No closed
PA or HA equivalence for the polynomial is asserted here.

## Independent replay

- Main source SHA256:
  `ae84b5cec4b26455f45031882d082edd40b701e5cfe8515e5f5b4f97fdeed1fc`.
- Checks source SHA256:
  `eeaa76a3496981349c240a04a3e91d2d76e70438a0c53c5941f90b849ab2c277`.
- Main object SHA256:
  `c3dc5a51b0ae05cf659d976123a4710a1d6c3e7baebb93286d3ca64498c92147`.
- Checks object SHA256:
  `e87eccac6dcfa95bc6169a90afa97754177dbc350207d7d8f4fc636b7353c3d3`.

Both commands used `-M6000 -j1 -DElab.async=false` and one Lean thread,
fresh regular output files, a private overlay, package-only fallback and
the 512 MiB disk reserve. Main and Checks took 11.282 and 2.487 seconds.
Both objects, complete logs and all 20 axiom reports match the author's
accepted final pair. Main is silent; the reports use only standard Lean
axioms (`propext`, `Classical.choice`, `Quot.sound`). No warnings or errors
were accepted.

The exact zero-refresh profile is 191 cached modules, including 95 Foundation
modules, 476 cached artifacts, 41 boundary primaries with 123 companions,
and 640 selected first artifact providers. Before and after compilation,
the executed driver made 3,594 authenticated comparisons over 1,331 paths.
It also checked the author's complete four-attempt history and 40-file
manifest; the first three attempts remain recorded as authored.

Durable evidence is in
[the ROOT replay packet](arithmetic-control-frame215-root-replay.json),
[its manifest](arithmetic-control-frame215-root-replay/FILES.json), and
[the author receipt](arithmetic-control-frame215-author.md).
Terminal metadata has regular hardlink copies; the independent proof
objects were produced by the ROOT compiler invocation.
