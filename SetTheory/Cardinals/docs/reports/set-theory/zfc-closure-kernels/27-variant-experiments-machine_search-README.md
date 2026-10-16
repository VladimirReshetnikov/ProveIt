# A four-row reassociation of the 253-state machine

This contribution supplies a complete binary Turing machine with **253 working
states**, start state 0, blank symbol 0, and a distinct terminal state 253. It
ties the existing 253-state construction. It reaches the same complete
post-initialization configuration **40 moves earlier**: 312,935 moves instead
of 312,975. The two endpoints agree in state, head position, and every tape
cell.

The table is `grammar_search/candidate/faster253.tm`, SHA256
`d5b7a357dbf4dd9d18c8e1aa04dc0c3c0e1b8f349853b7558d1a096a15684412`.
Only four compact transition rows differ from the pinned upstream machine:

| State | Read | Upstream action | New action |
|---|---|---|---|
| 37 | 0 | 0 R 41 | 0 R 42 |
| 37 | 1 | 1 R 42 | 1 R 48 |
| 42 | 0 | 0 R 50 | 0 R 41 |
| 42 | 1 | 1 R 48 | 1 R 50 |

The transformation reassociates a closed sequential decoder region from
`(A,(B,C))` to `((A,B),C)`. No logical axiom, proof enumerator, or register
operation is changed. `PROOF.md` gives the ordinary mathematical proof of
same halting behavior. The proof has finite computational certificates and
reuses four already proved register-file lemmas. A new Coq proof object has
not been generated or checked.

## Reproduce the included candidate

From this directory, with Python 3 and assertions enabled:

```sh
python grammar_search/verify_candidate.py
python grammar_search/strict_affine.py
python grammar_search/independent_rm_check.py
```

The first command checks input pins, the literal table and state bijection,
the complete finite bootstrap using an independent sparse simulator, and
the 2,981-pair register-program bisimulation in both directions. It also
repeats the original affine diagnostic. The second command applies an
explicit stricter port of the rules in the published `M253.SymExec` proof.
It checks the register named by each decrement guard, allows only the
single-effect box states used by the Coq definition, and counts positive
progress only from literal machine transitions. All **8,391** instruction
cases pass; every case has at least **13 literal transitions**, in addition
to any accelerated scans or proved register-file excursions. Negative checks
reject an unguarded decrement, a decrement guarded on the wrong register,
remarking an already incremented file, and a corrupted decoder row. The
third command rechecks the RM certificate with an independently written
tuple/bit-prefix interpreter, without importing the generator's string and
integer execution functions.

Neither command downloads dependencies or invokes a proof assistant. Both
write a small result JSON in `grammar_search/candidate/`. The committed
results accompany the source. To reconstruct the finite RM certificate,
run `python grammar_search/make_certificate.py`; its independent checker is
`grammar_search/prior_rm_verify.py`.

The exact common endpoint is dispatcher state 33, head position -17, gap
40, all-zero normalized instruction pointer, and source-order registers
`[5,0,0,0,2,0,0,0,0]`. There are 158 spare blocks, with nonzero values 1 at
spare indices 2 and 8; all other spare blocks are zero. The result JSON
records all 178 positions containing a one. This is the 330th register
configuration after the standard initial vector `[2,0,0,0,0,0,0,0,0]`.

## Search performed in this contribution

The first stage enumerates all **238** single local operations exposed by
the source-09 closed-region reassociation generator at its 203-node
baseline. Its concrete backend reuses old decoder entries, checks all
runtime cases, searches for a finite bootstrap landing in one of the first
2,000 register configurations, and prunes states only from combined runtime,
bootstrap, and protected-box coverage. A trial bootstrap is limited to
750,000 literal moves. Candidates with zero-run greater than 7 or depth
greater than 39 are excluded by the selected backend constraints.

| Outcome | Count |
|---|---:|
| All affine cases and a matching finite bootstrap passed | 146 |
| Affine execution did not pass | 26 |
| Bootstrap reached the finite fuel limit | 6 |
| Bootstrap actually halted | 1 |
| Excluded by the selected shape constraints | 59 |
| Total | 238 |

The smallest complete emitted table in this stage has 253 states. The
successful state counts are recorded individually in
`grammar_search/results/single_rotation_results.json`. No smaller example
was found.

Four subsequent greedy direct-redirection searches retain all 55 protected
box transitions and recheck runtime, bootstrap, and coverage pruning after
each accepted deletion:

| Initial rotation index | Initial states | Final states | Affine candidates tested | Box-filtered candidates |
|---|---:|---:|---:|---:|
| 0 | 253 | 253 | 55,692 | 504 |
| 49 | 256 | 253 | 116,269 | 504 |
| 232 | 254 | 254 | 56,166 | 506 |
| 233 | 253 | 253 | 55,692 | 504 |

The index-49 search accepts `61 -> 260`, `45 -> 17`, and `32 -> 262` in old
labels, with revalidation after each step. The final exact bootstrap is
312,975 moves. The remaining searches accept no deletion. These are
specified finite experiments; their negative outcomes do not establish a
state-count lower bound or exclude other encodings, mutations, proof
systems, initializers, or search schedules.

Optional replay commands, which take several minutes, are:

```sh
python grammar_search/cost_search.py
python grammar_search/greedy_folds.py --index 0
python grammar_search/greedy_folds.py --index 49
python grammar_search/greedy_folds.py --index 232
python grammar_search/greedy_folds.py --index 233
```

## Provenance

The baseline 254-state table is by **Mira-Cult**. Jeff Ketchersid's upstream
project supplies its Coq verification and the affine/run-length proof
architecture. The existing 253-state reduction is by **mira-emmy**, in
`jeff87654/busy-beaver` PR 20, pinned to head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`. The included upstream files are
read at this exact commit. The baseline 254-state table has SHA256
`d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb`;
the upstream 253-state table has SHA256
`84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.

The decoder inventory, prior rotation utilities, prior finite-RM checker,
and prototype wrapper are from Vladimir Reshetnikov's ProveIt report host,
pinned to `4747142d5d15213eb711bdadfa3cc7e769fcb7a7`, under
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/`:

- `code/09-decoder-decoder-search-dag_tools.py` -> `dag_tools.py`;
- `code/09-decoder-decoder-search-rotate_search.py` -> `rotate_search.py`;
- `code/09-decoder-decoder-verify.py` -> `prior_rm_verify.py`;
- `code/04-machine-engineering-context_search.py` -> `prior_context_search.py`;
- `code/04-machine-engineering-analyze_table.py` -> `analyze_table.py`;
- `data/09-decoder-machine-data-decoder_entries.json` -> `decoder_entries.json`.

These are retained unmodified. The new files are `cost_search.py`,
`greedy_folds.py`, `make_certificate.py`, `verify_candidate.py`,
`strict_affine.py`, `independent_rm_check.py`, the candidate, its certificate, and the present results
and notes. The graph reassociation is an established semantic operation;
the particular four-row candidate and measurements are this contribution.

The inherited Wade framework notice is retained as
`upstream253/ZF/generator/LICENSE.wade`. It applies to Wade's framework;
the original source attribution and other inherited notices are preserved.
No bundled file is relabeled as exclusively authored by this contribution.
`MANIFEST.json` records every delivered file's hash and the source pins.
