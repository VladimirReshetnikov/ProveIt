# Independent runtime audit of the claimed 245-state construction

Status: ACCEPTED for the runtime/composition layer on the ordinary mathematical-certificate basis. The full `--whole-frame --literal` replay completed with exit code 0 in 356.814 seconds. No runtime proof gap was found in the reviewed inference machinery.

## Exact object

Canonical table SHA256:
`17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13`.

Old-label table SHA256:
`f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267`.

Independent parsing establishes 245 working states, canonical labels 0 through 244, 490 binary rows, start 0, and separate target-only halt 245. Every move is L or R. The supplied bijection maps the complete old-label table exactly onto the canonical table. Fresh grammar emission reproduces the supplied table byte-for-byte.

## Independent replay outside the archive's executables

`audit245_runtime_independent.py` imports the previously recovered and reviewed prefix246 affine engine. It changes only the common source/target padding from 40 to 64, parses the new source-site and table files as data, and independently checks:

- All 6,460 ordered source operations and operands match the original parsed program.
- The new source tree is complete and prefix-free; maximum path depth 51, maximum zero run 6.
- All 8,391 guarded instruction cases pass, using 3,306,645 symbolic rules. Minimum positive literal progress is 13 moves.
- All 8,390 nonhalting residual pointers normalize to new source leaves without changing the represented complete tape.
- The invariant gap increment is 0 in 6,456 cases and 1 in 1,934 cases; it never decreases.
- All 42 inherited macro-support transition rows remain literally unchanged.
- Exact state count, canonical renumbering, and table hashes pass.

Evidence: `audit245_runtime_independent.json`.

## Trusted mathematical rules inspected

The archive's inherited macro-induction checker and affine engine are byte-identical to the previously reviewed prefix246 files. Its padding/import adaptation is separately checked by exact source-text equality.

The actual-table macro audit resets its derived-theorem tables, binds the proposed 245-state table, and freshly derives four one-block traversal lemmas. Each block lemma has an arbitrary natural block value and untouched opaque contexts. Unary self-loop acceleration is induction on the represented nonnegative length. Finite-list acceleration is admitted only after a same-state, same-orientation, context-preserving block theorem has been established. The list carry normalization is the free-word identity C(A)1 = 1B(A), together with reversal.

The three arithmetic contracts and nine register-selection contracts are then derived from those rules. Decrement requires the named register and the correct zero/positive guard; a register box already carrying an effect cannot silently receive another effect. All 342 oracle-gate checks and all actual-table macro obligations pass.

The expanded whole-frame checker removes opaque register boxes. With `--all-values`, each of the nine primary registers has an independent arbitrary natural variable; the selected decrement register is exactly zero or one plus an arbitrary natural. The gap has another variable. The spare suffix consists of an arbitrary first block and an arbitrary finite tail, so it is genuinely nonempty. All run lengths are checked nonnegative. A non-self-loop branch is allowed only with a provably positive constant prefix. Remaining opaque list traversal is derived by the block/list induction just described.

Successful endpoints require the complete frame, exact symbolic head displacement, and strictly positive finite time. Residual-pointer normalization is a finite word identity extended by the same arbitrary zero gap, not a test at a few gap values. These are ordinary mathematical induction certificates suitable for composition inside ZFC. They are not a newly checked Lean/Rocq endpoint or a serialized ZFC proof object.

## Finite checks versus universal claims

Blank initialization is one exact finite computation, audited separately by the parent and again by the full verifier. Literal fixtures are finite regression checks and do not establish arbitrary-register behavior. The universal runtime claims rest on symbolic run/list induction and the complete set of source instruction cases. A finite symbolic rule limit can reject an unresolved proof but does not weaken a successfully closed universal case into bounded-register testing.

Source-program bisimulation and logical consistency calibration are being reviewed in a separate mathematical audit. Ordered-leaf equality alone is not used here as a substitute for that review.

## Reproduction and preservation

Full command, run in a writable copy:

`python3 -B research_sub246/verification/audit245_runtime_copy/code/verify_all.py --whole-frame --literal --output research_sub246/verification/audit245_runtime_replay`

The original extracted archive remains untouched. Fresh logs and certificates are under `audit245_runtime_replay`; the top-level log is `audit245_runtime.log`.


## Final full replay

The complete verifier returned `PASS_245_DELIVERY`:

- 293 delivered artifact hashes verified.
- Exact emitted canonical/old-label tables and printed table agree with the certificates.
- Actual-table macro induction and all 8,391 affine instruction cases pass.
- Expanded all-values whole-frame proof: all 8,391 cases, 2,312,645 symbolic rules, all 490 transition rows covered, minimum 13 literal moves. Exact head displacement is checked for every nonhalting case. This pass took 348.285 seconds.
- Independent residual-frame normalization: all 8,390 nonhalting successors pass.
- Independent grammar and 54 immediate bootstrap-lock equations pass.
- 1,410 scanner contractions and an exact 407,915-step startup pass.
- All 8,385 freshly regenerated finite literal fixtures match the frozen inputs and pass; every one of the 490 rows is exercised, with maximum 2,686 moves. This is additional finite regression evidence, not the source of universality.

Final machine identity is unchanged: canonical SHA256 `17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13`, 245 working states, 490 binary rows, separate halt 245.

Primary fresh certificate: `audit245_runtime_replay/verification-summary.json`. Expanded proof results: `audit245_runtime_replay/core/whole-frame.json`. Actual-table derived macro traces: `audit245_runtime_replay/core/runtime/macro-inductions.json`. The independent recovered-engine result remains `audit245_runtime_independent.json`.
