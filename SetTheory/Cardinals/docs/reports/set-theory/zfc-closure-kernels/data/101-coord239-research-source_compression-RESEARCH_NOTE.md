# Source compression and register permutation results

## Validated 239-state candidate

The helper-search teammate supplied three candidate tables. This subtask
validated the variant with new transition `80/0 = 0L106`, leaving the logical
source and physical register assignment unchanged.

`helper91_target106_239_full_runtime.json` records the complete unbounded
runtime PASS: **8,386 guarded source cases, 2,330,575 symbolic rules, all 478
transition rows exercised, and minimum constant instruction duration 13**.
The four register-block traversal schemas were rederived from the actual
table. The inherited verifier covers nine independent arbitrary natural
register values, an arbitrary nonempty finite spare list, and arbitrary extra
gap. It uses literal steps and ordinary induction on unary lengths and finite
lists; it is not a proof-assistant kernel theorem.

The old-label table SHA256 is
`76a9574ac0385b96dbd558fa852a222e1d9025e48e34dc3590384146726d2a9b`.
A separate C++ blank run reaches the same primary register frame as the
240-state baseline after **409,835 steps**, head -5, gap 181, and 176 total
register blocks. The parent is checking the complete tape and final theorem.
The full verifier is `verify_helper106.py`; its candidate table is
`helper91_target106_239.tm`.

## Baseline

The input is `candidate-rotation240` in ProveIt commit
`13ec39ed43148b1807f51ed6e6528e1c84659562`. It has 240 working states, inherited
start 95, dispatcher 96, separate halt 254, and a 6,455-leaf source. The source
list SHA256 is `74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d`.
No repository file was edited.

## Physical register permutations

All 36 physical transpositions were constructed by conjugating the non-engine
register-skip targets. Each passed a discovery sample of 313 guarded symbolic
cases from 223 diverse source leaves: 11,268 checks in total. This sample alone
does not certify all instructions of all 36 variants.

A literal bootstrap census, bounded at 5,000,000 steps per table, found 31 clean
frames, four fuel limits, and one actual halt. The fuel limits were swaps
(1,7), (1,8), (2,5), and (4,6); they do not prove noninitialization. Swap (6,7)
actually halts and is rejected. Nineteen clean frames satisfy the sufficient
safe condition that logical formula fields R1, R2, and R5 are zero.

Swap (0,1) reaches a particularly simple frame: all nine logical registers are
zero after 68,835 steps, head -3, gap 71, and 63 total blocks. It also received
an entire unbounded runtime replay: 8,386 cases, 2,329,001 symbolic rules, all
480 rows, and minimum constant duration 13. Its physical map is
`(6,2,1,4,3,7,8,5,0)`. Its table SHA256 is
`788bc00d537888a01c04b9ea51c323224e522701ae97b278afac7db6c42f64c1`.
This remains a **240-state** result. The teammate's stated same-head and
incoming-only fold searches found no reduction among all 19 simply safe
variants. Those are finite negative controls, not lower bounds.

The bootstrap census records all primary values and the block count, but not
the complete spare array in JSON. A full tape replay is needed if the
permutation table is promoted independently.

Material files: `permutation_screen.py`, `permutation_screen.json`,
`bootstrap_permutations.cpp`, `bootstrap_permutations.json`, `perm_0_1.tm`,
`verify_permutation.py`, and `perm_0_1_full_runtime.json`.

## Source-fragment screens

The inherited arithmetic-signature screen was rerun on the current source.
It found 225 distinct trees including leaves and 49 closed fragments of at
most 60 leaves touching at most three registers. Their bounded arithmetic
signatures had no collision. This is a proposal screen, not a proof of
universal inequivalence.

A constant-domain analysis with atoms 0, 1, 2, 3, and at least 4 reached 6,452
source leaves after 64,724 work-list iterations. It found two forced-zero
decrement sites. One transfer from R1 to R6 is a no-op at one of its 128
occurrences, so it is not a removable shared fragment. No smaller table was
inferred from these observations.

Material files: `semantic_fragments.py`, `semantic_groups.json`,
`zero_specialization.py`, and `zero_specialization.json`.

## NIP specialization and concrete failure

The previously proposed NIP specialization assumes R6 is zero at entry. It
halts exactly when R5 is one, otherwise drains R5 to zero and retains the old
stack pop. Its scalar tree is

```
(CD5, ((CD5, ((CD5, CC1), CB1)), HALT)).
```

The current check has 12 leaves; the specialized scalar check has six. This
uses an entry invariant, not an arbitrary-register identity. Its complete
source DAG still has 202 distinct nodes, matching the current baseline.

A new finite syntax enumeration considered all six-leaf binary trees with
three decrement leaves, one halt, one continue, and one break: 63,000
assignments, of which 11,058 had valid local paths. Six candidates matched the
destructive exact-one test on inputs 0 through 16. Their full-source DAG sizes
were 204, 202, 204, 204, 204, and 203. Only the known specialization has its
previous ordinary loop proof; the other five remain finite proposals.

A naive literal implementation retained 240 states and changed these rows:

```
46/0: 0R17 -> 0R62
46/1: 1R62 -> 1R78
62/0: 0R77 -> 0R53
62/1: 1R78 -> 1R77
77/0: 0R88 -> 0R103
```

It passed 25 local guarded cases and failed three. All three are genuine
errors: the new CB1 at path `111010010101011`, CI2 at `111010010110110`, and
CI5 at `11101001011110` produce the wrong whole tape on both all-zero and
all-one register files. On all-zero inputs they redispatch after 628, 634, and
636 steps, respectively. Six complete traces are retained in
`nip_literal_counterexamples.json`.

State 46 also serves a return route. Treating it as a private decoder state
breaks that route. This literal table must not be promoted as a consistency
candidate. Source-changing searches stopped after the 239-state helper
candidates were found and tested.

Material files: `test1_trees.py`, `test1_trees.json`,
`nip_specialization240_sites.json`, `nip_specialization240.tm`, and
`nip_literal_counterexamples.json`.

## Attribution

The calculus, register program, and original 254-state construction are due
to Mira-Cult; the original verification is due to Jeff Ketchersid; the compiler
framework is due to Andrew James Wade. Existing ProveIt reductions and
incoming sources 73, 74, 76, and 80 retain their credit. The runtime verifier
used here is copied from those pinned sources, not newly authored or claimed
as an independent checker. Parent-level exact startup, mathematical proof,
source calibration, license preservation, and artifact selection are separate.

## Independent audit and source bridge after discovery

`UNIVERSAL239_AUDIT.md` reviews the inherited symbolic runtime rules, their unbounded mathematical scope, the clean-path/zero-padding bridge, positive simulation, exact source calibration assumptions, and ordinary ZFC provability versus a proof-assistant endpoint. The independent source extraction in `source_bridge/check_source_bridge.py` freshly parses the actual three pinned Lean definition files, evaluates the complete routing lookup tree, and reconstructs the unchanged 6,455-leaf source byte for byte. Its snapshots and receipt are in `source_bridge/`.

The independent open-tape local checker `check_local_blocks_239.py` proves all four exceptional target106 blocks, with the single reachable-only neighbor guard explicitly delegated to the universal guard certificate. The separate `audit_input_and_boot_clock_239.py` validates the exact candidate table/source and checks that the old blank startup visits the four exceptional rows 18, 12, 6 and 3 times. Their expansion overhead is 144 steps, predicting the selected target106 startup at 409,835 steps; it also checks every required guard during that old startup. These two short checks have executed PASS receipts in `local_blocks_239_independent.json` and `input_boot_clock_239.json`.
