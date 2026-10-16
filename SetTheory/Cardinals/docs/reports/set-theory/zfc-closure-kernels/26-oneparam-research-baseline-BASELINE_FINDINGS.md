# Upstream machine audit and new bounded merge experiments

Research snapshot: 2026-10-16. This file records one subtask's results for the
main report. It contains no claim of a new consistency-equivalent machine.

## Pinned upstream baseline

The default branch of `jeff87654/busy-beaver` was pinned at
`297ab8df7e5de329605c3875b4934643b371a5e3` (2026-10-15). Its ZF directory calls
the Mira-Cult machine with 254 working states its smallest verified machine.
The actual current comparison must also include open PR20, whose head is
`0d544f2a2e3c18f12278441a74b7879f31cbe856`. That PR gives a 253-state machine,
including initialization, and a Coq development of its exact blank-tape
halting/refutation equivalence. It was open and mergeable when inspected.

Primary sources:

- https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/README.md
- https://github.com/jeff87654/busy-beaver/pull/20
- https://github.com/jeff87654/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/README.md
- https://github.com/jeff87654/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/tools/generate_candidate.py
- https://github.com/jeff87654/busy-beaver/blob/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/m254/coq/e2e/E2E254.v

The 253 table is a complete binary machine, start 0, separate uncounted halt
253, 506 transition rows, SHA256
`84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.
The original 254 table has SHA256
`d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb`.
The 253 construction changes the following rows in the old 254 labels:

| Old state/read | Write | Move | Target |
| --- | --- | --- | --- |
| 3/0 | 0 | L | 48 |
| 5/0 | 1 | R | 97 |
| 5/1 | 1 | R | 64 |
| 49/1 | 0 | R | 5 |

Old state 8 is removed. Old state 5 becomes compact start 0. Old dispatcher
96 becomes compact state 33. The old terminal 254 becomes compact halt 253.
These old labels are a proof/analysis view, not extra physical states.

The PR reports a clean rebuild of 160 modules, 194 closed assumption reports,
and recursive `coqchk`. This subtask inspected sources and reproduced the
literal construction and finite bootstrap; it did not rerun that Coq build.
The endpoints are external theorems in the Coq metalanguage:

    halts tm c0 <-> SIR ⊢TC ⊥
    halts tm c0 <-> ZFc ⊢TC ⊥
    halts tm c0 <-> (ZFc + AC) ⊢TC ⊥

The upstream README explicitly makes no additional internalized-proof or
independence claim. The target `ZFc` is the library's closed-schema ZF without
regularity; `AC` is its choice-set axiom. The separately formalized relative
consistency of regularity supplies the bridge to conventional ZFC. The main
report must distinguish this external theorem from the requested assertion
provable *inside* ZFC about its arithmetized consistency predicate.

Attribution: Mira-Cult designed the original 254 machine, calculus and
nonextensional theory; Jeff supplied the accepted Coq verification; mira-emmy
supplied the public 253 reduction and table-specific verification; Andrew
James Wade supplied the compiler framework. The link to the original
Mira-Cult repository returned 404 through the GitHub connector in this session;
the public Jeff source preserves the literal table and attribution.

## Logical and compiler architecture

The accepted 254/253 program uses nine registers and a three-phase
single-marker interpreter. The final decoder has 6,460 instruction sites,
6,459 internal binary nodes in its expanded prefix tree, and depth at most
34. A path-bisimulation certificate connects this decoder to a 219-node
shared Wade program. Its eight logical rows include a single implicational
axiom, quantifier rules and equality congruence. One gated bundle emits
container and global-image-collection instances.

The nonextensional theory SIR consists of equality laws, container axiom CP,
global-image collection GIC, and irreflexivity IR. CP and GIC already suffice
for the bisimulation-quotient interpretation of ZF: this is the upstream
theorem `S0_equicons`, not a new result. IR is essential to the current code
convention: formula code 1 aliases `v0 ∈ v0` with falsity, and it also handles
allowed parameter collisions. Dropping IR from the *machine logic* without
changing this coding is unsound, even though the clean theory S0 is itself
equiconsistent with ZF.

Similarly, Yedidia–Aaronson's historical 7,910-state construction targets a
stronger stationary-Ramsey consistency principle; its row in a historical
record table should not be labeled exact Con(ZFC). The dated 745 or 432
records are irrelevant as present optimization thresholds. The actual
public comparison is 253, with 254 as the accepted default-branch reference.

## Experiment A: local-window macro folds on the actual public 253 table

ProveIt's `public253_fold_search.md` explicitly left this experiment unrun.
We used its exact pinned `audit_tm.py` at ProveIt commit
`6ec2e80dbbe45a99b7812fb5757977307959a51e`. The local copy's Git blob SHA1 is
`d4716e5b82a9ec6683614d43b2c2a2f8a141e346`, matching the fetched source.

The checker computes a finite overapproximation of blank-tape reachability
by head-centered windows. Shifting the window admits both possibilities for
the incoming unknown cell. For every possible window at a removed state p,
the original and the redirected p→q machine must reach a common configuration
within the known window in positive numbers of steps on both sides. This is
a sufficient stuttering simulation condition. It differs from demanding
exact agreement at the register-machine dispatch boundary.

| Radius | Maximum steps per side | Abstract configurations | Ordered pairs | Survivors |
| --- | --- | --- | --- | --- |
| 4 | 64 | 31,909 | 63,756 | 0 |
| 6 | 128 | 335,369 | 63,756 | 0 |

At both radii every one of the 506 state/read pairs remains abstractly
possible. All 253 working states are graph reachable, and ordinary
step-by-step bisimulation gives 253 singleton working classes after 13
refinement rounds. The simple startup-reuse test has no candidate: the start
has another reachable incoming edge, and no other state has its zero row.

The radius-4 run independently replayed 312,975 blank-tape moves. The result
was compact state 33, head -17, with 178 one cells, fingerprint
`5f59972252d34cd6a0e4660a65e5ae7409381d00d2a0182e11830224ea77aa5b`.
This is the advertised complete bootstrap endpoint. The evidence does not
claim that no earlier dispatch visits occur or that this prefix alone proves
future correct execution.

Files: `audit_tm.py`, `public253_macro_r4.json`, `public253_macro_r6.json`.
Reproduction uses the command-line options recorded in each JSON's input and
local-search sections; `--trace-steps 312975 --self-test` was used at radius 4.

## Experiment B: mixed-row amalgamations

Fixed-target state folding keeps both transition rows of the retained state.
The new experiment instead takes the read-0 row from one member of a pair
and the read-1 row from the other, with both orientations checked. All
incoming edges to the removed state are redirected, including outgoing
self-references, and its two rows are deleted.

We considered 224 states: all working states except 28 fixed register-box
states and the dispatcher 96. Every candidate must preserve all 55 protected
register-box rows literally *after* target redirection. Thus the reused
symbolic register-box summaries still have the same underlying table.

| Category | Count |
| --- | --- |
| Unordered state pairs | 24,976 |
| Mixed construction choices | 49,952 |
| Constructions whose two mixed rows differ from either unmixed choice | 49,426 |
| Rejected because a protected box row changes | 886 |
| Box-preserving constructions tested | 49,066 |
| Box-preserving genuinely mixed constructions | 48,552 |
| Affine survivors | 0 |

The machine, register program and unchanged upstream affine-executor hashes
were checked, as was exact reconstruction of the public 253 table. All
8,391 baseline instruction cases passed. A candidate is first tested on
baseline cases whose explicitly executed rows it changes. If all those pass,
it must then pass a complete 8,391-case recheck. Unaffected traces are unchanged
by induction because all hidden box rows remain identical. No candidate
reached the survivor stage.

The failure breakdown matters: 44,836 candidates exhausted the 1,000-iteration
affine fuel limit; 4,027 violated the symbolic geometry handled by the model;
203 returned an unexpected terminal status. Fuel exhaustion is not a proof
that the candidate lacks a longer correct simulation. A symbolic geometry
failure can also mean a limitation of the executor. These are bounded
failures to establish the fixed dispatch interface, not lower bounds on
arbitrary consistency-equivalent machines.

Files: `mixed_merge_search.py`, `mixed_merge_results.json`,
`summarize_mixed.py`, `mixed_merge_summary.json`; helpers under `helpers/`;
the pinned table/program/executor files are under `busy-beaver/ZF/`.
The raw result SHA256 is
`3257f92df606b653956f5d4d6ad812eb9181c37addde1a04cea9af31cf0f89a9`.
The summary driver checks that the raw evidence names the exact current
search-driver SHA256.

## Assessment and next optimization target

No new 252-state complete machine was found. The known public 252-state
runtime body remains a prepared-input result because removing the shared
initializer breaks the established blank bootstrap. The new experiments
strengthen the evidence against a quick fixed or mixed one-state fold under
the current interfaces, while leaving substantial search outside these
families.

The most useful next compiler work is a joint search over decoder structure,
runtime phase guards and initialization, with a certificate expressing the
exact boot endpoint and all symbolic dispatch cases. The missing initializer
cannot be ignored in the count. Changes to a box helper need new box proofs;
the preserved-row test should be enforced after every target rewrite.
At the theory level, prospective syntactic savings should be evaluated by
the generated complete table only after both consistency directions are
proved. A shorter formula that loses a required container/collection clause
is not an optimization of the same consistency strength.
