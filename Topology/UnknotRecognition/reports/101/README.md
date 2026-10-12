# Occurrence-preserving flag regularization of compressed normal cuts

Research continuation prepared for the ProveIt project, 12 October 2026.

The article proves a linear-encoded-size regularization theorem for coherent
three-dimensional affine polytopal atlases, an explicit **4,607 T** family
bound for the canonical raw normal cut of a `T`-tetrahedron source, and an
exponential lower bound against a tempting globally stable rank-refinement
strategy. It supplies a generic compiler, independent replay, a finite
source importer, and an executed bridge to the preceding Morse-certificate
code. Ordinary barycentric subdivision is classical; the contribution is
its compressed, occurrence-preserving construction and accounting.

**Scope:** This is not an unrestricted quasi-polynomial unknot recognizer.
The full nonzero native normal-cut atlas exporter is proved as a construction
but not implemented here. Matching discovery, native geometric/patterned
transport, admissibility repairs, and global hierarchy bounds remain open
integration obligations. The generic validator does not certify manifoldhood.
No production files were patched, and no native knot-recognition benchmark or
full upstream regression suite was run.

## Read and reproduce

`article.pdf` is the compiled 27-page article. `article.tex` and the two small
generated table files under `results/` rebuild it. The article contains full
proofs, counterexamples, measurements, a claim ledger, and eight research
priorities. `SOURCE_AUDIT.md` and `provenance/sources.json` record the review
boundary, source revision, exact fixture, and third-party hashes.

From this directory, using Python 3.10 or newer (tested with Python 3.13.5):

```sh
python -B -S tests/test_flags.py
python -B -S code/check_publication.py
python -B -S code/demo.py --mode solid-torus
python -B -S code/demo.py --mode periodic --bits 1024
python -B -S code/demo.py --mode convex --copies 1
```

The `-S` option disables site packages: the delivered runtime and checks need
only the Python standard library. A generic invocation does **not** assert a
ball or knot verdict. The convex demo returns a source-bound collapse witness
only for the explicitly constructed disjoint convex-polytope copies.

To rerun the larger audit or replace the retained timing data:

```sh
python -B -S code/audit.py
python -B -S code/benchmark.py
sh build.sh
```

The benchmark overwrites its JSON and TeX tables. Text in the article records
the delivered completed run; review that text before publishing new timings.
`build.sh` requires a LaTeX installation with the packages named in the source.
No Python topology package, external algebra system, or network connection is
required. Expanding finite references is intentionally capped.

## Executed evidence

There are **32 passing unit tests** and **448 counted symbolic replays** in the
retained audit. That audit includes all 145 one-tetrahedron partial-face-pairing
inputs in its stated enumeration: 70 pass the no-face-holonomy source contract
and 75 are rejected; acceptance is not a manifold certificate. The audit also
checks all 24 relabellings of the repository's exact zero-cut solid-torus
fixture, 33 convex-copy cases, 300 seeded product cases, 11 second subdivisions,
and five binary stress cases up to 16,385-bit namespace bounds.

On the native source fixture the regularized cell counts are `(8,38,54,24)`.
A direct local-tetrahedron flag quotient, independent of the source importer
and compiler, agrees. These are actual source-fixture tests, not live calls to
`fastunknot.normal_cut_cell_complex` and not tests of all normal vectors.

Paired complete local representation queries show a **23.93x** median paired
literal/encoded ratio at 256 segments (50,176 represented cells), and a
**0.192x** ratio at one segment: encoded is slower on the smallest case.
Both arms construct, check, and serialize a representation; their formats
differ, as explained in the article. All raw samples and A/A controls are
retained. An earlier 1,024-layer pre-timing literal comparison exceeded the
whole-command limit; its partial log is retained, and no timing for that
case is claimed. These are not whole-knot recognition speedups.

## Layout

- `code/`: convex/source atlases, compiler, independent replay, literal oracle,
  finite tetrahedral importer, Morse adapter, audits, demos, publication check.
- `tests/`: positive, adversarial, source-oracle and binary-size unit tests.
- `examples/`: three complete source-bound replayable JSON examples.
- `results/`: completed audit, every timing sample, pilot limitation, logs and
  generated tables.
- `third_party/`: the preceding Morse arithmetic module and CLI, unchanged
  except that the CLI filename is renamed; original license retained.
- `provenance/`: source metadata and copied dependency hashes.

`INTEGRATION.md` gives safe intake steps and the required native-exporter
contract. `SCHEMA.md` documents the binary atlas and certificate formats.
`CLAIMS.md` distinguishes proved statements, executed evidence and obligations.
`MANIFEST.sha256` protects file integrity, not geometric source authenticity.
