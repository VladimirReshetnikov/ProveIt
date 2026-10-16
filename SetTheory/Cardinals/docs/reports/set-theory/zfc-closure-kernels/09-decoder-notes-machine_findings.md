# Literal 254-state record: audit findings

## Outcome

**No machine with fewer than 254 working states on a blank tape was established.**
The useful concrete results are a252-state prepared-tape core, a correct
experimental267-state emitter for a202-node register-program DAG, and a
subsequent reduction of that emitted machine to 256 states. These are actual
transition tables, not estimates obtained by adding a decoder-node count to
an assumed fixed overhead. A fully self-contained Python audit and exact
tables are in `machine/`.

## Published baseline and record convention

The machine is Mira-Cult's `zfc_254.tm`, mirrored in Jeff's
busy-beaver repository and the ProveIt import at
`67086c8d8802ea7b3625a2fc0765d39e2181e335`. Its exact byte SHA256 is
`d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb`.
There are254 working states, each with two transitions, plus a terminal
state that is not counted. It starts in state 0 on a two-way infinite all-zero
binary tape. The new tables preserve old numeric labels, so working-state
count is the number of rows divided by two, not the maximum numeric label.

The upstream proof commit
`c132d7eae8158cd3a9850ea3eb7251158c3dd821` is dated 2026-10-14. Its
`ZF/m254/coq/e2e/E2E254.v` contains direct halting equivalences to syntactic
inconsistency of SIR, the library's ZF presentation, and ZFC. This is the
appropriate benchmark for the user's exact target; independence alone would
not suffice. The original compiler bundle is incomplete in the supplied sources; the
frozen, formally verified mirror is the reproducible starting point.

Primary sources:

- <https://github.com/jeff87654/busy-beaver/tree/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254>
- <https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/coq/e2e/E2E254.v>
- <https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/design/tm.md>

## Positive verification results

| Machine | States | Initial tape | Affine cases | Gap lower bound | Blank initialization |
|---|---:|---|---:|---:|---|
| Published baseline |254|blank|8,391 pass|40|264,982 steps|
| Prepared core |252|explicit finite seed|8,391 pass|40|not supplied|
| Re-emitted decoder |267|blank|8,391 pass|41|264,982 steps|
| Re-emitted decoder after eleven folds |256|blank|8,391 pass|41|264,982 steps|

Each complete check comprises 8,387 normal,3 overflow and1 halt obligation.
The published program has 6,460 leaves, with both zero and positive cases
required at each decrement site. Baseline nonhalting obligations use
1,937,942 abstract steps in total, at most331 per case, with at most4
dispatch-root visits. Including the halt case gives1,937,955 abstract steps.
These are steps of the affine executor, not actual TM runtime estimates.

The register file and a free natural gap parameter are treated symbolically.
Four register-box contracts—mark/skip, increment, zero decrement and positive
decrement—are inherited from the existing generic development. The audit
checks55 conservatively protected transition pairs against the exact
baseline. This is Python evidence under those contracts, **not a newly
kernel-checked full equivalence theorem**. The companion compiler certificate
is separately needed for register-program equivalence.

For all three blank-tape machines, a literal finite simulation checks the
entire initialization tape exactly after 264,982 transitions: state 96,
head -8, gap 62, nextproof 2, and all other primary registers zero. This
supports the bootstrap lemma without making any inference about the
subsequent infinite computation.

## Concrete reductions and their limits

From every valid dispatch configuration, original state 8 is unused and
state 5 reads only 0. Its read-0 transition equals state 48's read-0
transition. Redirecting5 to 48 and removing8 gives252 working states. Both
states participate in initialization from the blank tape, however. The
prepared252 seed explicitly encodes the dispatch marker, zero gap, header
and registers, so this does not improve the blank-tape record.

The compiler experiment reassociates the register program from 203 to 202
hash-consed decoder nodes while preserving its maximum zero-run length7.
Its path depth increases34→35. Re-emission initially costs267 working
states because old contextual sharing is lost. The following substitutions
were then accepted, and the entire affine suite and exact initialization
were rechecked after each one:

`15→299, 11→303, 22→298, 61→298, 188→282, 244→275, 245→286,
174→256, 45→299, 32→300, 178→206`.

The final256-state table is transition-closed without any unread-target
rewiring. Pruning the 267-state intermediate requires three such rewrites:
the transitions at(178,1), (188,0), and(61,0) point to 0 instead of discarded
states. Each pair is absent from the full affine/initialization/oracle
coverage union; the actual pruned table is then rechecked. All these
details are machine-readable in the package.

A201-node candidate with zero-run length8 and path depth52 passes8,353
cases but fails38, even at gap bounds56 and58. The candidate is therefore
rejected as a literal-machine implementation. Program DAG size is an
insufficient optimization objective: context-specific state reuse, valid
dispatcher words and bootstrap cost must be included.

## Negative search scope

Finite searches tried all 252 blank initial states for the runtime core;
all 1,012 choices for the newly available state 5/read1 transition with state 8
removed; all 253 starts after folding5 into48 but retaining8; and504
single-bit prepared starts corresponding to a one-use extra helper state.
No valid initialization was found within2–3 million steps per candidate.
The initialization acceptance test allowed nextproof, param1 and prooflist
to vary while requiring other primary registers to be zero.

A final directed fold search around the 256-state table, excluding protected
engine states, root 96, and bootstrap states 5/8, checked57,375 candidates
with no survivor. It is bounded by 500 affine-executor fuel per case. A
separate last bootstrap-fold search checked255 replacements for state 8 and
the 5→48 replacement. Exact domains, fuel limits, finite tape bounds and
execution totals are in `machine_audit_results.json` and the package logs.
None of these negative searches is a minimality theorem.

## Recommended next implementation target

Use the frozen254 table as the counted baseline and optimize the **actual
transition table** as the search objective. Maintain a certificate consisting
of program equivalence, all dispatch sites, explicit box-transition
preservation and exact initialization. A decoder reduction that loses old
sharing can cost states; a runtime-only reduction that loses initialization
also cannot count as a record. The new theory simplification developed by
the theory agent is a more substantive prospective source of savings than
the fully saturated one-state folds explored here, but it still requires a
complete recognizer and literal compilation before any state claim.
