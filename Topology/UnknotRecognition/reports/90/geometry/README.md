# Unsaturated interval-bundle attachments

This package extends the incoming marked-parallelity terminal classifier to
allow full annular interfaces whenever at least one base boundary component is
not attached in its entirety. It computes exact handlebody genera and component
counts, without expanding numerical genus or multiplicity.

The main mathematical result is stronger than a homology formula. An orientable
interval bundle over a connected bordered surface B, attached along a nonempty
proper subset A of its boundary, adds exactly `a - chi(B)` genuine 3D one-handles
after interface collars are absorbed. Here a counts interval components of A.
The free product and handlebody genus contributions are
`1 - chi(B) - c`, where c counts entire attached boundary circles, plus the
attachment graph's cycle rank. Annular slopes do not change this conclusion.

The theory also localizes the remaining difficulty: a saturated base adds
`1 - chi(B)` one-handles and one two-handle. The implementation does not process
that remaining two-handle and returns `INCONCLUSIVE` on saturated bases.

## Scope

- The finite input is conditional on actual embedded interval bundles and core
  handlebodies. Scalar profiles alone are not geometric certificates.
- The native adapter retains and independently replays the incoming source
  parallelity, ordered interface, and raw core-cancellation proofs.
- The output is an unmarked terminal census, not transported peripheral words,
  an explicit large band system, or a standalone knot-recognition verdict.
- Closed bases, saturated bases, unsupported core cancellations, and resource
  exhaustion remain inconclusive.
- The relative surface-spine and handle arguments are classical ingredients.
  The contribution here is their exact use at this source-interface boundary,
  the nonabelian condensation, and an independently replayed native extension.
  No exhaustive external priority or novelty claim is made.

## Files

| Path | Role |
|---|---|
| `article/unsaturated_bundles.tex` | Full proofs, ball criterion, counterexample, saturation corollary |
| `article/unsaturated_evidence.tex` | Coverage and timing discussion/table |
| `code/unsaturated_bundles/finite.py` | Finite producer and strict exact input validation |
| `code/unsaturated_bundles/replay.py` | Independent graph/relative-handle recount |
| `code/unsaturated_bundles/native.py` | Source-bound adapter and full proof replay |
| `evidence/native_audit.json` | Complete retained 106-case coverage run |
| `evidence/*_certificate.json` | Five newly covered actual inputs with portable source proofs |
| `evidence/benchmark.json` | Five paired timing rounds and binary-genus examples |
| `evidence/upstream_dependencies.json` | Exact 30-module incoming dependency hashes |
| `evidence/unit_tests.txt` | Fourteen completed test methods |
| `tools/vendor_upstream.py` | Reproduce the minimal pinned incoming runtime |

## Reproduction

The finite kernel and its tests use only Python's standard library. Run from this
package root:

```bash
PYTHONPATH=code python -m unittest discover -s tests -v
```

The native adapter requires the `runtime/fast` directory of
`ProveIt_Unknot_Marked_Parallelity_2026-10-12.zip`. It can be on PYTHONPATH directly.
To copy only its pinned transitive dependencies, run:

```bash
python tools/vendor_upstream.py --runtime PATH_TO_INCOMING_RUNTIME_FAST --output vendor
PYTHONPATH=code:vendor python -m unittest discover -s tests -v
```

All 30 source modules are copied byte-for-byte with hash checks. The generated
`__init__.py` files are explicitly minimal reproduction namespaces; they avoid
the unrelated imports in the public `fastunknot` facade. They are not patches to
the maintained repository.

Regina is needed only for the independent expanded-cut oracle. The retained run
used Regina 7.4. To repeat the native audit and paired benchmarks:

```bash
PYTHONPATH=code:vendor python tools/native_audit.py --corpus vendor/marked_parallelity_research/corpus.json --output evidence/repeated_native_audit.json
PYTHONPATH=code:vendor python tools/benchmark.py --corpus vendor/marked_parallelity_research/corpus.json --output evidence/repeated_benchmark.json --rounds 5
```

The audit must not be run with arbitrary incomparable corpus/source revisions.
The dependency and corpus hashes in `evidence/upstream_dependencies.json` pin the
exact baseline used for the 30-to-35 coverage comparison.

## Findings

On the retained 106 source cuts, the old disk-only classifier completed 30 and
the new classifier completed 35, preserving every previous census. All 35
completed source proofs replayed; every newly covered case agreed independently
with Regina's explicit cut and handlebody recognition.

The newly covered fixtures are small, and the compiled Regina oracle was faster
than the Python source-certificate path. The improvement established here is
coverage and removal of a structural annular-interface restriction. It is not a
measured small-instance speedup or an end-to-end quasi-polynomial recognizer.

The 16,385-bit genus example is a finite conditional model. It classifies a
handlebody whose relative construction requires `2 * (2**16384 + 17)` one-handles
using a binary count. The prototype does not construct that many bands.

## Next research steps

1. Emit source-addressed compressed band systems and transport an existing
   boundary pattern through the collar reductions. The existence proof alone
   does not bound the encoding of this transport.
2. Combine the proper-boundary reduction with the separately proved saturated
   disc-base absorption and its raw geometric cancellation certificate.
3. Compile the single remaining two-handle per saturated base as a compressed
   geometric attaching curve. A bound on relator count is insufficient without
   a bound on these words and their embedded interpretation.
4. Use the nonabelian free-product decomposition to extract certified core-group
   obstructions when unsaturated attachments are the only remaining bundles.
5. Measure the distribution of saturated bases after actual hierarchy cuts,
   and charge descriptor construction, source replay, and marking transport
   separately in the global complexity account.
