# Two new 194-state PA consistency machine designs

Prepared for Vladimir Reshetnikov, 15 November 2026 (UTC).
Source snapshot: `2ca99e3d23a5397aae4c786f4da7dfe1cca87f85` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/2ca99e3d23a5397aae4c786f4da7dfe1cca87f85).

## Result and proof status

No valid blank-start machine below 194 working states was established.
The main new construction is **PA194AX11HC4**. It preserves the exact source
of the revised AX11H packet and changes six selector rows to implement a
four-cycle of physical register positions. Its 194-state binary transition
table is distinct from all 526 spanning 194-state classes in the recognized
current corpus. Exact blank startup takes 57,406 transitions. All 4,778
source outcomes pass the supplied universal literal check with positive
affine clocks and four list lemmas derived from its own transition rows.

The mathematical argument combines the new physical simulation with the
revised AX11H packet's **written iPRA calibration** to obtain

    iPRA proves: Con(PA) iff PA194AX11HC4 does not halt from blank.

The PA-refutation predicate is the fixed current Foundation predicate used
by that supplied calibration. This is an ordinary mathematical proof with
an explicit inherited dependency, not a new completed Lean/Rocq build.
An incomplete formalization does not mean the written iPRA proof is absent.
Read `report/report.pdf`, `construction/ax11hc4/PROOF_TRANSFER.txt`, and
`comparison/WRITTEN_PROOF_AUDIT.txt` for the exact proof boundary.

**PA194C32** is a companion physical construction for the original primary
PA194 source. It changes seven rows, has 194 states, passes all 4,780
literal outcomes, and initializes in 56,250 transitions. Its directly
proved new result is blank halting equivalence with that older primary
source. The principal absolute iPRA consistency claim belongs to AX11HC4,
which preserves the revised calibrated source exactly.

Both machines have a two-way infinite, initially all-zero binary tape,
head at coordinate zero, dense working states 0 through 193, initial state
0, and terminal label 194. Native tables use initial label 74 and terminal
label 254. The halt label is not counted as a working state. Every working
state has two transitions. Lines are `state read write L/R next_state`.

| File | SHA-256 |
|---|---|
| `construction/ax11hc4/machine/pa194_ax11hc4.tm` | `fe4253a42045c330a499d99cc33d55a14e116cae910eb624c499161a7a7ca755` |
| `construction/cycle32/pa194_cycle32.tm` | `3af42ea9d430e5df22b69e6fc540e3530f87263372580c7c554bae37ba524ac8` |

## Contents

* `report/`: complete report, LaTeX source and generated data/table inputs.
  The PDF contains both complete 388-row tables in readable paired columns.
* `construction/`: both accepted physical tables, label maps, compact full
  source grammars, standalone reconstruction, two source simulators,
  universal literal checker, exact clocks, startup receipts, proof notes,
  imported interpreter and licenses.
* `references/ax11h_calibration/`: ten original written proof components,
  original README and claims, with pinned Git-blob source identities.
* `comparison/`: all 526 spanning 194-state class representatives, two
  separately recorded nonspanning byte forms, the 89 source-attributed
  positive classes, 33 mechanism families, recursive occurrence inventory,
  historical catalog, exact novelty code, positive controls and receipts.
* `research/startup193/`: the rejected runtime-only 193-state cores,
  complete two-edit pools, finite bootstrap screen and completed results.
* `research/parameterized_generalizer/`: a new 189-token source experiment
  that compiles to 196 states, with its written semantic identity and
  reproducible compiler checks. An additional unproved 188-token search
  is clearly separated from accepted constructions.
* `validation/`: completed portable replay log and final release/PDF check receipt.
* `SHA256SUMS`: hashes of the distributed files before any replay rewrites
  generated receipts. `verify_release.py` verifies these and runs checks.

## Quick replay

Use Python 3.10+ and Node.js 18+ with no third-party packages. Do not use
`python -O` or set `PYTHONOPTIMIZE`: the inherited checkers use assertions.
From the package root:

```sh
python3 -B verify_release.py
```

This checks the release hashes, reconstructs both tables into a temporary
directory, checks both exact blank startups and all source outcomes in
Python and JavaScript. To include the full literal-clock checks and the
526-class exact novelty replay:

```sh
python3 -B verify_release.py --literal --novelty
```

These optional checks have already completed successfully on the delivered
tables. The literal checks regenerate receipt files in place; subsequent
hash verification should be done against a fresh extraction. Individual
commands, from `construction/`, are:

```sh
python3 -B reconstruct.py --output /tmp/pa194_c32_rebuilt
python3 -B ax11hc4/reconstruct.py --output /tmp/pa194_ax11hc4_rebuilt
python3 -B verify_source.py
node verify_source.cjs
python3 -B ax11hc4/verify_source.py
node ax11hc4/verify_source.cjs
python3 -B verify_literal.py C32
python3 -B verify_literal.py HC4
```

For the structural novelty replay, from the package root:

```sh
python3 -B comparison/novelty.py \
  construction/ax11hc4/machine/pa194_ax11hc4.tm \
  construction/cycle32/pa194_cycle32.tm \
  --output /tmp/pa194_novelty_replay.json
```

The novelty test checks exact transition tuples under arbitrary control
renaming, every possible root, reflection, global bit exchange, and ignored
halt-entry write/move decorations. Bit exchange here strengthens structural
comparison; it is not asserted to preserve computation on blank zero tape.
The census covers recognized literal `.tm` files, including nested archives
and all 139 historical 194-state keys (including 43 without a declared
start). Arbitrary unrecognized JSON-only/code-only/prose encodings and all
machines outside the pinned corpus are outside its claimed scope.

## Optional unsuccessful reduction searches

`construction/SEARCH_METHOD.txt` gives the two completed local-contraction
commands. Each tests all 18,721 unordered control pairs in a sound
radius-six window overapproximation, with at most 32 old and 32 new local
steps. Neither finds a compatible two-branch contraction.

`research/startup193/README.md` gives the two-edit startup commands. The
combined run covers 22,575,210 blank starts and 4,167,291,032 transitions,
with zero complete source-frame hits. The 20,202 bounded outcomes remain
unresolved. These are reproducible finite negative results, not a lower
bound of 194 states and not a divergence proof for every trial.

The generalizer experiment has 196 states and is not a frontier result.
Its 189-token source is shorter than its parent's but creates more reader
subtrees. The additional 188-token interface search reaches 195 states
and lacks the required all-store completeness proof; it is not an accepted
consistency machine.

## Rebuilding the PDF

With a normal TeX Live installation including Latin Modern, AMS packages,
microtype, geometry, booktabs, enumitem, xurl, hyperref and fancyhdr:

```sh
cd report
python3 build_report_data.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The report input tables are also distributed, so Python is not required
merely to recompile the supplied LaTeX.

## Attribution

The source calculi, original programs, unary machine machinery, compiler
ancestry and inherited written proofs remain attributed to their original
authors. See the pinned source links and manifests, `NOTICE.txt`, and the
retained upstream licenses under `construction/licenses/`. The new work
comprises the two exact physical allocations, their checks and mathematical
transfer, the comparison, the finite reduction searches, and the separately
identified generalizer experiment.
