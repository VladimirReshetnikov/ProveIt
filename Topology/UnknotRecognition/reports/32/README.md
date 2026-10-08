# Graded occupancy and four-strand torus-block scanning

Research package for `ProveIt/Topology/UnknotRecognition`, 8 October 2026.

**Read:** `article/graded_torus_scanning.pdf` (source alongside it).

## Mathematical contribution

The paper proves a local cancellation bound sensitive to maximum **absolute
homological–quantum bidegree occupancy**, rather than just total matching
population. Graded residue homology transfers any relative comparison model's
object bounds to every exhaustively reduced scan. Applying Kelomäki's 2025
four-strand torus Morse-model theorem gives a specified fixed-finite-field
scanner with tilde-O(n^3) bit complexity and tilde-O(n^2) space on expanded
standard four-strand torus words, retaining every homological degree.

For s-strand words partitioned into t embedded four-strand torus blocks with
repetition counts m_i and d isolated defects, the proved population envelope is

    R = 9 * 3^d * (2^s A)^t * product((m_i + 1)^2).

The constant A comes from the cited model, independently of the input. Full
homology computation takes poly(n,s) * 2^O(s) * R^3. At fixed strand count,
t = O(log n), d = O(log^2 n) give quasi-polynomial **full unknot decision** for
one-component closures in this syntactically certifiable class.

This is not a general quasi-polynomial recognizer. The proof imports the stated
external Morse-model result and standard Khovanov/unknot-detection theorems.
No independent proof of the entire external Morse construction, formal Lean
verification, or priority claim is made.

## Executable contents

- `src/graded_scan.py`: exact F_2 bigraded disk-braid scanner with absolute shifts,
  local FIFO cancellation, same-pivot rebuild control, alternate pivot order,
  independent old scalar reducer, exact graded closure, and safe resource errors.
- `src/graded_cube.py`: independently assembled small closed crossing cube.
- `src/block_plan.py`: Pareto planner and literal block-certificate verifier.
- `vendor/`: unchanged geometric and algebraic code from the prior radical-transfer
  research package; not the current production fastunknot source tree.
- `tests/`, `experiments/`, `results/`: tests, all recorded validation data,
  operation counters, timing batches and their limitations.
- `integration/`: integration contract and proof obligations; not a blind patch.

Python 3.10+ and the standard library suffice. No network is used by the code.

```sh
python -m unittest discover -s tests -v
python experiments/validate.py
python experiments/check_bounds.py
python experiments/growth.py
python src/graded_scan.py --strands 4 \
  --word '[1,2,3,1,2,3,1,2,3]' --audit
python src/block_plan.py --strands 4 \
  --word '[1,2,3,1,2,3,-2,-3,-2,-1]'
```

Run `make paper` to rebuild the article and `make test` to run unit tests.
`make benchmark` may take substantially longer than validation; see the run
notes. LaTeX sources, tables, and the PDF are included together.

## What was actually checked

The unit suite passes 24 tests. The independent validation covers 175 input
words/closures, 355 scans, 1,488 audited prefix reductions and 67,474 checked
entries. Sixty cases also compare with the unchanged earlier reduced-cube
oracle. No failure was recorded. These are finite checks, not a proof for all
inputs or a database of 175 distinct knot types.

A separate structural run completed torus words through 48 crossings, a mixed
opposite-sign block example, and weaving controls. The observed torus peak
occupancy of nine is **not** asserted as a universal theorem.

Timing compares the new local schedule only against a same-pivot rebuilding
ablation, not against the maintained production recognizer. Two longer batches
were interrupted by outer execution timeouts; all completed cases and the noisy
retry are retained. No missing timings are imputed. The data do not establish a
production-wide speedup.

## Output and limits

Only one-component closures receive `UNKNOT` or `KNOTTED`; other closures receive
`LINK`. The rank-two criterion is justified in the paper. Time and allocation
limits produce `NO_VERDICT` / exceptions, never an inferred knot answer. Integer
and rational Khovanov homology are not computed. All asymptotic bounds use the
expanded word length, not the encoded size of binary exponents.

The deterministic theoretical bounds use guaranteed dictionary/indexing
operations. The prototype uses Python dictionaries. The default trace retains
only scalar counters; requesting all prefix profiles is an additional audit
output not included in the stated space bound.

## Integration

The reviewed repository commit is
`ca4681932655c2898d3ea65611bb74ba988b87d0`.
The current production scanner has a different internal representation from
this archived reference harness. Follow `integration/INTEGRATION.md`; do not
replace maintained files with `vendor/`. The current complete production suite
has not been run on this prototype. No repository or Library files were modified.

See `PROVENANCE.json`, `CLAIMS.md`, and `SHA256SUMS` for dependencies and audit
status. Code and original article text are provided under MIT-0; cited external
papers remain under their respective authors' licenses and are not bundled.
