# Machine-encoding work at pinned ProveIt source

No machine with fewer than 246 working states was established by this work.
The most useful findings are an exact phase-collision obstruction for the
borrowed-tail arithmetic core, and two literal 202-node source variants.
Both source variants emit complete 264-state Wade tables. Their logical
contracts and source correspondence are distinct from the missing new
blank-tape binary calibration. Read `mp_first_source_contract.md` for one
source variant and the sections below for the newer work.

All repository input was read from shared sparse snapshot `../source` at
commit `7ba1598461c6e485c5aeb8f673c0b1d571f8012b`. No upstream repository was
changed. Generated sources/tables below are research artifacts, not asserted
new Busy Beaver records.

## Measured routes

All generic counts below are actual complete Wade emissions with every source
edge re-extracted. Maximum zero-run is the source decoder metric; it is not an
unconditional model of the custom prefix246 state cost.

| Route | Live source nodes | Max zero-run | Wade states |
| --- | ---: | ---: | ---: |
| Original full logical/theory grammar, fixed bundle layout | 206 | 7 | 268 |
| Fixed C(0,1,2), all original logical axioms and gates | 217 | 8 | 280 |
| Fixed G binders, fresh k=c+1 or c+2 | 215 | 7 | 277 |
| Both fixed, k=c+1 | 221 | 7 | 283 |
| Both fixed, k=c+2 | 221 | 8 | 284 |
| All/Eq radix4 tag swap | 206 | 7 | 268 |
| Dual rho6 plus independent EFQ(a) | 209 | 8 | 272 |
| Dual rho6 plus EFQ(b) or EFQ(c) | 210 | 8 | 273 |
| DoubleB6 replacing Comm | 211 | 7 | 273 |
| Corrected MP-first on fixed-layout grammar | 207 | 7 | 269 |
| Corrected MP-first on prior source201 | 202 | 7 | 264 |

The fixed C/G measurement comprises 1,800 grammar trials; tag swap, corrected
MP-first and DoubleB6 each 3,000; dual+EFQ comprises 9,000. These are bounded
search scopes, not lower bounds. The logical worker supplied separate
calibration arguments for proposed basis changes; no new full binary
calibration is asserted by these cost experiments.

## Rejected-code diagnostic

`mp_first/` retains an early cost-only candidate whose direct NIP pop failed
the intended overwrite-H contract. `mp_first_contract_tests.json` explicitly
records `DETECTED_SEMANTIC_DEFECT`. Do not use it as a consistency machine.
The corrected candidate adds clear-H before pop; the corrected tests and
source contract are named explicitly.

## Detector and arithmetic diagnostics

`return_context_census.json` separates the 1,402 offending return48 contexts
where the cell immediately left is one: 323 increments, 1,076 zero-decrements,
and three explicit breaks. Every positive decrement in this diagnostic
satisfies the zero-neighbor condition. The source-path census is useful for
conditional compiler designs, not itself a universal runtime theorem.

`repair_right_scanner.py` deletes detector74, directs58/0 rightward to84, and
checks all one-additional-row substitutions on rows of the first rejecting
trace. Its ledger has the exact bounded scope, fuel failures and survivors.
This is distinct from the context worker's leftward-shortened detector family.

`specialized_axiom_compiler.py`, `mp_first_from201.py` and `rotate_variants.py`
are new orchestration code using attributed unchanged pinned backend helpers.

## Reparameterized source with optimized helpers

`permuted_prefix_helpers_right.json` is the logical worker's reparameterized
AX word over the already optimized original203 helper library. It has
202 nodes, maximum zero-run 7 and maximum path 95. The complete original AX
word reproduced through this helper mapping has exactly the original AX
ordered normal form. More strongly, the logical worker independently checked
all 20 individual helpers via guarded instruction-CFG bisimulation, erasing
only control-only jumps and commuting consecutive increments by register:
see `../logical_routes/helper_correspondence.md` and its checker/results.

`emit_source_wade.py` emitted `permuted_prefix_wade/candidate.tm`: 264 states,
SHA-256 591f6a95273c7f9cfd7f2b26de7665c6eed99015fddb59397b7cfbc860797b24,
with all source edges re-extracted. A further 50,000 safe-associativity proposals
retained 202 nodes and zero-run 7 while shortening the path 95→84; see
`permuted_prefix_rotated_best.json` and its rotation report.

The finite-dictionary MILP did not improve this202-node incumbent. Initial
balanced-seed restricted dictionaries were infeasible under zero-run 7;
a rightward-seed solve timed out after 120 seconds with a worse 204-node witness.
The generic global grammar sampler also did not improve the incumbent.
The earlier `permuted_rotation` experiment used a depth bound excluding its
initial95-deep seed; it is not meaningful evidence against a feasible search
and should not be cited as one. The corrected `permuted_prefix_rotation`
allowed path ≤ 100.

These are future compiler inputs, not custom prefix246 tables. Historical
`decoder_entries` mappings are context-sensitive hints, not valid generic
entry points, and were not used to claim a new small machine.

## Borrowed-tail return: exact phase collision

The arithmetic worker's proposed 245-state partial core deletes 255 and uses
75/0=0R63,48/0=1L131,131/0=1L126, with final spare 1. The local arithmetic
identities have a separate symbolic proof. I investigated repairing126/0 and
its sole old decoder incoming108/0.

`borrowed_tail_pruning_audit.json` certifies that 977 of 980 choices for 126/0 choices have a
rejecting symbolic prefix that never reads108/0. For the other 3 choices,
`borrowed_tail_context_repair3.json` exhausts all 980 choices for 108/0 repairs. There are
no survivors. This is a complete bounded screen of that 980² two-row family
by safe prefix pruning, not an impossibility theorem: the oracle can reject
unsupported trajectories or exhaust its 2000-rule fuel.

A sharper obstruction is fully literal. `check_borrowed_tail_collision.py`
replays two valid instruction configurations:

- CI at PC 11101001001000010110, logical register 6;
- CI at PC 11101001001000101010, logical register 1.

Both start with every physical primary register 1 except the selected register 0,
spare list [1], and header distance 40. At steps 405 and 357 they have identical
complete tape, head 11 and state 126, although the required successor PCs differ.
Neither free 126/0 nor potential repair 108/0 has yet been read.
`borrowed_tail_exact_collision.json` records every literal transition.

`borrowed_tail_first_collision.json` pinpoints the loss: one step earlier,
the runs have the same tape and head 13 but states 48 and 112. The proposed edit
makes both zero rows exactly 1L131, so they merge at state 131/head 12. A repair
only after that merge cannot recover which source PC was present. This
obstructs a unique first-correct-return interface; it is not a theorem against
all possible future code, alternate simulation relations, or different
program encodings.

The arithmetic worker then proposed preserving the header bit at 57/1 and/or
30/1 before the collision. `borrowed_marker_search.json` screens all 3 nonzero
write-bit choices together with126/0 and108/0 repairs using the same safe
pruning. All fail, already on the zero/positive CD 8 source cases at PC 000.
The arbitrary left context of the new arithmetic lemmas is preserved by the
affine oracle used for these marker tests.

## Direct-architecture component packing (03:48 UTC)

New separately generated libraries in `component_packing/`:

-217 working states for retained-query133/native68/writer11/comparator29,
 preserving five distinct unlinked return ports and all four counted failure
 states. All mathematically allowed rows pass exact projection checks;
 5,224 whole-component regressions compare2,269,330 literal steps.
-188 states without comparator, with three unlinked returns and three counted
 failure states;3,280 calls compare1,965,106 steps.
-62-state unconditional native-edge quotient, saving six states by full binary
 control bisimulation, independent of read guards.

`component_packing/PROOF.md` states the generalized guarded-congruence theorem,
ordinary guard assumptions, state ledger and missing linking obligations.
`rebuild_certificate.py` regenerates exact table hashes from finite quotient
certificates without repeating search. These are prepared-frame libraries,
not complete blank-tape machines; the188-state library does not implement the
proposed saturation flag suffixes. No sub246 consistency TM is established.

A final admitted-graph reachability certificate removes the unused query
prefix000 role, giving216 and187 states respectively. Final directories are
`component_packing/final_with_compare` and `final_without_compare`; all ports
and counted failure states remain distinct. The complete regression suites
and deterministic table rebuilds pass again. New internal query entry points
would require redoing this unreachable-role proof.
