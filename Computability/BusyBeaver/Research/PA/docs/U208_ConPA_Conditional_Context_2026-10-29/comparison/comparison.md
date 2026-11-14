# Comparison of the six supplied U209 submissions

## Scope and principal finding

This analysis uses `VladimirReshetnikov/ProveIt` commit
`343da82d7384d10ec9fd1c17361fc923b2d1d117`, with the six ZIPs named in
`source_inventory.json`. Five ZIPs contain executable machine packages; the
ZIP whose name ends in `Joint_2026-10-29 (1).zip` contains a PDF only.

**There are only two machines up to rooted labeled transition-graph
isomorphism, not five or six independently different 209-state machines.**
The Plain, Compatible Folds, Composed, Joint, and PDF-only Joint tables form
one class. Compatibility forms the second class. Compatible Folds and the
full Joint ZIP contain byte-identical native and dense tables. Plain and
Composed differ only by permutations of a few internal decoder labels.

This statement was checked independently of every supplied checker, using
`inspect_tables.py`. The checker parses all literal rows, verifies totality,
the binary alphabet, directions, start and halt labels, and graph
reachability. It propagates the uniquely forced rooted map along read-zero
and read-one edges, preserving writes and directions. All 209 working
states and halt are graph-reachable in each table, so a consistent completed
map is a full isomorphism; a conflicting forced assignment disproves one.
This is graph reachability, not a claim that the blank run visits every state.

The PDF-only Joint is an especially important naming trap. Its Appendix B
was independently extracted to 418 rows, all of which match **Plain**
exactly. It does not identify the table in the full Joint ZIP byte-for-byte,
although that table is isomorphic. The PDF-only report describes a
30-rotation construction via Contextual U211, whereas the full Joint package
uses an explicit common source association. Its stated hash is accurate for
the machine actually printed in its appendix.

## Exact identities

The following hashes are SHA-256 of `machine/u209.tm` (or the independently
reconstructed PDF table). Every dense file includes its start header and has
418 transition lines, working labels 0 through 208, and separate halt 209.

| Submission | Dense table SHA-256 | Isomorphism class | Maximum source depth |
|---|---|---:|---:|
| Plain | `65ccb606c8e970adec22c311486e747b440171363601b8f11b56bc729cf8decb` | A | 42 |
| Compatibility | `bda91bd40880f96edef104246d22797fe281355cf03610ab7e93e7923be8aa16` | B | 41 |
| Compatible Folds | `5ded628d692ff442e4346c61eb3db3c77b0ac2c80c1ecced45cbfc483be40e08` | A | 42 |
| Composed | `3a69998d818b6e637e33dc0a2412538e49179a501496d5c252c7f68ff2af78be` | A | 42 |
| Joint (full package) | `5ded628d692ff442e4346c61eb3db3c77b0ac2c80c1ecced45cbfc483be40e08` | A | 42 |
| Joint (PDF-only) | `65ccb606c8e970adec22c311486e747b440171363601b8f11b56bc729cf8decb` | A | 42 |

The four class-A executable packages have byte-identical source occurrence
maps, SHA-256
`cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164`.
Compatibility's map has SHA-256
`912724f29b0de28b3326c710fdf1f3863ebd07058c6db1a9b4bbaffb3ae5e3f3`.
It changes precisely 720 leaf addresses relative to A.

All five maps contain the same 3,909 ordered opcode/operand pairs, and all
resolve to the same 5,083 guarded ordinal control edges. An independent
prefix-interval resolver in `inspect_tables.py` rechecked this equality. All
maps have maximum consecutive-zero run six. The supplied audited builders
also give 197 distinct syntactic subtrees in each case.

### Explicit isomorphisms

The following permutations use native labels, with all unlisted labels
fixed. They preserve start 0 and halt 254 and conjugate every literal row.

* Plain to Compatible Folds or full Joint:
  `217→129→214→217` and `215→204→216→215`.
* Plain to Composed:
  `215→129→204→214→216→215`.

These two short permutations explain why distinct file hashes and different
construction recipes should not be counted as independent state-count
improvements. Complete dense isomorphisms and nonisomorphism witnesses are
recorded in `independent_comparison.json`; `comparison.json` additionally
records the nontrivial native maps.

For Plain versus Compatibility, the forced map conflicts along the graph
edge word `000000100100000001001101100111111110`. This is a path in the
transition graph, not a proposed actual tape history. A deterministic
rooted labeled isomorphism must preserve every such edge path, so the
conflict suffices even when the edge word is not realizable by one tape.

## What the constructions share

The common U212 ancestor has three deletions previously realized separately
by Contextual, Research, and Rotated U211. The U209 proposals arrange a
common source layout in which all three deletions coexist. They remove
native labels 180, 181, and 218. In class A the replacements are 163, 220,
and 157; in Compatibility the last stage replaces 180 by 216 instead of
163. These are contextual folds, not ordinary identical-row merges.

The common principle is that a state entered by a right-moving transition
which writes a fixed bit has a known predecessor cell. Two decoder modes
can therefore share one physical state when an existing helper recovers
the mode from that bit. The hard part is arranging source addresses so that
all incoming transitions have the required tags while preserving helper
entries from other parts of the interpreter.

Every construction retains the arithmetic-entry repair at native 171/read0,
changing its backward entry from state 7 to 205. The source decoder at 7
is shared with arithmetic execution; a source reassociation that forgets
this repair is invalid. The finite checkers explicitly test this case.

All proposals preserve the complete blank initializer. Their exact startup
check runs 48,140 transitions and verifies the complete canonical endpoint,
including 120 one-cells and both zero exteriors. The endpoint has native
state 84, head -2, source ordinal 136, header distance 56, registers
`[1,0,13,0,0,1,0,0,1]`, and 43 spare registers initially equal to one.
Preservation of this prefix is useful evidence about initialization, not a
proof of nonhalting.

## Individual contributions and relative strengths

### Plain

The Plain package offers the most explicit rotation ledger: 30 closed
reassociations from U212, then the entry repair and simultaneous folds.
Its local quotient proof separates 414 ordinary rows from ten exceptional
two-cell cases. It audits all final internal-prefix bindings against the
simultaneous quotient and includes thirteen damaged controls. It clearly
distinguishes intermediate source identities from valid interpreters:
seventeen intermediate layouts have a seven-zero source run, and only the
final six-zero layout is used for the runtime theorem.

It also contains the strongest separate logical research result among the
packets: a proof that deleting the native dominated propositional axiom
destroys the desired PA calibration. The proposed Boolean matrix interprets
implication by Boolean equivalence, membership as false, equality as true,
and quantification as identity. It validates the other rows and U covering
bundles but makes target 1 false. PA can formalize induction on reduced
derivations, proving the reduced calculus's target underivability. Thus,
assuming PA is consistent, the reduced system cannot still have a
PA-provable equivalence with Con(PA). The word “dominated” in this lineage
describes a bound on a numerical parameter, not logical redundancy.

### Compatibility

This is the sole second isomorphism class. Its substantive change is an
eight-factor reassociation across a shared runtime helper in a closed
720-primitive region. It changes 204/read1 while preserving the 204/read0
branch used after the backward selector has just written zero. This is a
more precise use of a context invariant than forbidding all edits to a
state with non-decoder entries.

The layout has depth 41, and its historical symbolic replay takes 1,248,748
inference applications versus 1,250,049 for class A. This measures the
verification trace, not the unbounded blank run's runtime. It provides a
fully checked U210 intermediate and local proofs for both later stages.
Its README accurately distinguishes freshly replayed original finite
checks from inherited original universal receipts.

For a minimization search, this package is useful as a genuinely different
address layout with the same source semantics; retaining both classes
avoids searching four renamings as though they were four unrelated inputs.

### Compatible Folds

This gives a clean simultaneous three-fold proof directly from its
reassociated U212 intermediate, with ten arbitrary-exterior cases, 414
ordinary-row identities, twelve negative controls, and optimized-Python
checks. Its final table is identical to full Joint. The presentation
emphasizes preserving all three helper contracts and moving the closed
tail to native 215 to free native 163.

### Composed

This supplies 30 rotations and a five-state label permutation, with an
explicit exact clock relation for the final fold stage,
`T_new = T_pre + 2*n3 + 4*n5`. The bound applies only after source
reassociation, not to U212 itself. Its grouped decoder-prefix audit is a
useful independent source interface check.

The package recovers and includes the U222 calibration archive directly,
repairing a documentation omission in the compact inherited ancestry.
This improves provenance accessibility; it does not give a different
209-state machine up to isomorphism. Its reproduction command rewrites
generated machine/evidence files, so our replay used a separate copy.

### Joint, full package

This gives the most compact complete runnable release among the executable
inputs and a direct 18-selector source association of a 3,096-primitive
region. It has non-mutating reproduction, explicit inherited dependency
binding, independent final prefix auditing, thirteen damaged controls,
and an independent C++ finite primitive executor. Its full machine is
byte-identical to Compatible Folds, so these are complementary evidence
presentations for one literal table.

Its additional searches record no direct state alias within 15 local
steps and no one-row opposite-tag fold within 17 local steps among the
tested family. The searches are explicitly incomplete. They do not
establish a 209-state lower bound or exclude source reassociation,
multi-row rewrites, longer macros, or invariants using more than one cell.

The full Joint package is a convenient evidence base for another class-A
reduction; Compatibility remains the distinct alternate source layout.

### Joint, PDF-only

The manuscript is readable and includes all 418 transitions, a complete
rotation recipe, and a detailed local proof. Its displayed machine is
Plain. Because its ZIP contains no scripts or source archive, its claims
about accompanying executable artifacts cannot be reproduced from that
ZIP alone. It should be catalogued as a report presentation of Plain,
not another independent machine package.

## Verification performed in this comparison

All five executable packages' advertised `--quick` commands were rerun
successfully in separate copies. This rechecked their manifests,
deterministic constructions, local folds, source bindings, exact startup,
and each command's documented extra finite checks. Logs and elapsed times
are in `replays/*.log` and `replays/quick_replay_results.json`.

The supplied **full symbolic-runtime derivations were not rerun during
this comparison task**. Their saved reports all identify 5,084 primitive
contracts with 418-row coverage. These are arbitrary-natural-register and
finite-list inductive contracts in the inherited engine, rather than 5,084
bounded numerical trials. A new candidate should receive a fresh complete
replay, not inherit the old pass flags merely because its source graph is
unchanged.

The engine implementations are correlated. Plain and Joint contain the
same `symbolic_runtime.py` hash
`61b9c66272e8fd149829177cc384013814aea3c6b3b6b6f48e462d3913ea2022`.
Compatibility, Compatible Folds, and Composed contain the same
`native_symbolic.py` hash
`b4ffbf783ee2895a3f4584ae72b4c5498bfd518aa6d774765f8d1e65ed7a3f9a`.
Diffing these two versions shows the same core inference rules, with
different native/legacy labels, import names, and an explicitly substituted
56-cell header base. Their agreement is not five independent validations
of the induction rules.

None of the packages supplies a newly compiled end-to-end Lean, Rocq, MM0,
or internal-PA proof object for its literal U209 table. They contain
ordinary mathematical reduction arguments and executable evidence, plus
inherited numerical-calculus and Theory U/PA calibration. K215's separate
ZFC theorem does not certify them. The appropriate comparison preserves
this proof-status boundary while recognizing that the local finite
simulation proofs are much stronger than blank-prefix testing alone.
