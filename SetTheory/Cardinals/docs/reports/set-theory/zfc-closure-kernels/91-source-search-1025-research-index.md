# Machine implementation, source bridge, and reduction studies

This directory contains implementation proofs and bounded reduction searches
performed against ProveIt commit
`6446ff5668307a2ac6aee1896037f0b792090389`. The baseline canonical 245-state
table has SHA-256
`17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13`.

## Positive results suitable for the main package

| Artifact | Content and scope |
| --- | --- |
| `audit_macro_fine_bridge.py` | Independently parses original Dag254 macros and the optimized fine vocabulary, builds the finite register product, and rechecks every edge with the upstream path interpreter. |
| `macro-fine-bridge.json` and `macro-fine-bridge-certificates.json` | All 19 macro substitutions pass for arbitrary initial values in all nine registers: 192 product pairs and 346 guarded decrement edges. Exact return values and divergence are preserved. |
| `macro-fine-bridge-proof.md` | Ordinary proof of the per-macro bridge, including commuting increments, closed continuation boundaries, and positive progress. This closes a source-contract gap that an aggregate AX spelling hash would leave open. |
| `whole_frame_dynamic.py` | All-values whole-frame replay for an explicitly supplied complete binary source tree, without importing old source interval assumptions or fixed leaf counts. It rederives the block, arithmetic, and selector lemmas on the actual input table. |
| `audit_frame_dynamic.py` | Separate standard-library-only audit of complete source trees, full-width residual pointers, state renumbering, and the exact complete blank frame. It can link to the actual all-values replay by hashes. |
| `mask32-positive-control/` | Freshly rebuilt and fully verified DNE mask32 construction with 245 working states. Its retained grammar has 128 rules. This is a neutral state-count result, not a sub245 construction. |

The mask32 canonical table hash is
`d193291ac92bc090a9b8a6e7d2c578928109633e12155cd0ce9fc1b5f66d2921`;
the old-label table hash is
`2d11111223320f268b0b808748d55317c2d312b3f8732611d990b4c248ad9ac1`.
Its explicit source has 6,366 leaves and 8,269 guarded cases. All cases pass
the complete symbolic frame replay, with 2,233,088 checked symbolic rules and
a minimum of 13 literal steps per instruction simulation. The proof covers
an arbitrary extra gap, nine independent natural registers, and an arbitrary
nonempty spare suffix consisting of a first natural followed by any finite
list of naturals. All four block induction lemmas, three arithmetic macros,
and nine register selectors are rechecked on the actual emitted table.

The independent audit checks all 8,268 nonhalting successor identities,
including three overflows, and preserves every trailing zero. The exact
407,915-step blank execution reaches the same logical seed
`(3,0,0,0,3,0,0,0,0)` as routing245. Its complete tape contains 351 one-cells;
all other cells are zero. Dense canonical renumbering is checked row by row.

The main incorporation subset from the positive-control directory is
`grammar128.json`, `machine/`, `whole-frame.json`,
`independent-frame-audit.json`, `build-reproduction.json`, and
`validation-reproduction.json`. The `runtime/` subdirectory is an immutable
snapshot used for this independent run; a main archive that already includes
the same runtime can retain one copy. Absolute historical command paths in the
reproduction records can be replaced by the corresponding packaged paths.
The wrong-entrypoint diagnostic files are incidental workflow logs and need
not be included.

The mathematical composition is: original per-macro contracts, the checked
macro bridge, the new AX RPN contract, modified-source register bisimulation,
and actual-table whole-frame simulation. The new numerical-calculus transfer
and the inherited ordinary ZFC calibration are separately stated proofs.
None of these records claims a new Lean or Coq endpoint.

## Blank-start classification and finder

`blank_start_classes.py` classifies every possible initial state before its
first one-write. Before that event the entire tape is blank, so the state
sequence is deterministic and different starts with the same first writer
are identical modulo translation and a finite blank prefix. Repeated states
before a first one-write give exact forever-blank cycle certificates.

`baseline-blank-classes.json` records all 245 starts. Eleven starts enter
silent zero cycles. The others fall into eight first-writer classes, at states
7, 20, 42, 75, 83, 95, 112, and 255. Five writer classes have simple proved
outward self-loops; classes 75 and 83 produce no accepted frame within two
million steps; class 95 reaches the exact safe root after 407,915 steps.
The latter is independently rechecked by a dense interpreter. A bounded
failure is explicitly not a proof of nonhalting or impossibility of a later
safe frame. This classifier remains useful if future grammar changes relax
the old bootstrap locks.

```sh
python3 blank_start_classes.py BASELINE_OLD_TABLE \
  --output baseline-blank-classes.json --limit 2000000 --padding 64
```

## Bounded state-deletion studies

The C++ studies use the inherited
`inputs/state_reduction/candidate245-literal-cases.txt.gz`, decompressed as
`candidate245-literal-cases.txt`. Its decompressed SHA-256 is
`71fd6d7d0460c3f920ba945c04f2e3a1b571ce070e445ae019417ff0d675abc1`.
The 8,385 resource fixtures exercise all 490 baseline rows; their longest
baseline execution takes 2,686 steps. Each proposed table is checked with
20,000 steps of fuel on the represented tape interval `[-64,1983]`.

These are discovery searches over a precisely described finite family.
Failure to complete the fixture checks within that fuel is not a theorem
that the candidate has no correct slower implementation, and these resource
fixtures are not a theorem that every tested configuration occurs from blank.

| Search | Enumeration | Outcome |
| --- | ---: | --- |
| `one_incoming_search.cpp` | 137 states with one non-self incoming row; 133,712 freely synthesized predecessor rows | No full literal survivor. |
| `two_incoming_search.cpp` | 54 states with two non-self incoming rows; 105,408 individual row alternatives; 56 combinations of individually passing alternatives | No full literal survivor. |
| `multi_incoming_search.cpp` | 52 states with at least three non-self incoming rows; 213,744 individual alternatives; 201,984 deletion combinations | No full literal survivor; initial combination limits at states 4 and 30 are recorded explicitly. |

The latter two searches retain the original state while testing each incoming
row separately, then delete the state when combining replacements. They
therefore enumerate the **separable** family: a joint repair whose entries
depend on each other can be excluded by the preliminary local filter. No
general state-minimality claim follows.

The local alternative always chooses a write bit, a direction, and any
remaining working state as destination. The old initial state 95 and
dispatcher 96 are excluded from deletion. All candidate records and exact
counts are in the corresponding `*-summary.json`, `*-local-candidates.txt`,
`*.stdout`, `*.stderr`, and `*-survivors.txt` files.

`multi_incoming_pruned.cpp` and `multi_incoming_csp.cpp` explore the retained
multi-entry products using finite failure traces. A choice for a replacement
row that is never read cannot affect that same failed execution. The former
uses this fact to skip suffixes in lexicographic enumeration; the latter
records exact finite-domain nogoods and solves the remaining product with
unit propagation and exhaustive branching. Their own reports state whether
the retained products were completed or a time limit was reached. These
passes have the same finite-fuel and separable-family limitations.

Both follow-ups reached their 180-second limits at state 4 and found no
survivor. The suffix-pruned run completed state 2's 1,920 assignments and
covered 2,812,110 of state 4's 80,990,208 assignments with 812,000 literal
executions. The nogood run also completed state 2 and executed 12,386 distinct
state 4 assignments; its remaining learned-nogood coverage was not counted.
Its coverage field is therefore explicitly a lower bound. Neither run closes
the large products left by the initial capped enumeration. The source files
and final reports are now frozen.

```sh
g++ -O3 -std=c++17 one_incoming_search.cpp -o one_incoming_search
./one_incoming_search candidate245-literal-cases.txt
g++ -O3 -std=c++17 two_incoming_search.cpp -o two_incoming_search
./two_incoming_search candidate245-literal-cases.txt
g++ -O3 -std=c++17 multi_incoming_search.cpp -o multi_incoming_search
./multi_incoming_search candidate245-literal-cases.txt
```

For the two optional pruning passes, compile the similarly named C++ source
and pass the fixture file followed by `multi-incoming-local-candidates.txt`.
The local ledger must come from the preceding complete local-alternative
enumeration on those same fixtures.

## Rejected implementation prototypes

`scanner_contraction.py` deletes scanner state 58 and changes row `(41,0)`
to `(0,L,84)`. The resulting 244-state table does not pass the inherited
affine checker: the first failed case has source pointer
`11101001001000000`, physical register 2, and the zero decrement branch.
`scanner-contraction-result.json` records the exact failed obligation. This
is a certification failure, not a machine-minimality theorem or a claimed
literal counterexample.

`specialize_h1.py` attempts a direct test for `H=1` in the halting source
fragment. The proposed literal patch retains 245 states and fails the
unrelated `CI` case at pointer `01010`, because the patched state is reused
in another fused context. `h1-specialization.log` records that failure.
The specialized table and sites are rejected prototypes and must not be
presented as a certified construction.

`review_fine_compiler.py`, `fine-compiler-review.json`, and
`fine-compiler-review.txt` record the earlier review of the unchanged-source
fine-token compiler and its exact-table macro support. The later modified
source needs the additional per-macro and calculus bridges documented above.

For a compact main archive, keep the source files, small reports, proof notes,
and compressed fixture; compiled binaries and duplicate uncompressed fixtures
are unnecessary.
