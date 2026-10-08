# Compressed certificates for unknot recognition

Research continuation for ProveIt, 8 October 2026.

The article develops three exact local components: arithmetic-progression
certificates for compressed overlaps, complete congruence families for framed
regular-cover gluings, and independently checked primitive extreme normal
disks. It includes full proofs, bit-cost accounting, positive and negative
measurements, an archived algorithmic ablation, and 18 proposed research
questions. **It does not prove a general quasipolynomial unknot-recognition
bound.**

The main article is
`article/unknot_compressed_certificates.pdf`. Its main TeX file and all included
sections, figures, and figure-generation code are supplied. In the release
archive these files are under
`Topology/UnknotRecognition/research/20261008_compressed_certificates/`.

## Results and interfaces

- `fastunknot/compressed_endpoint.py` certifies an endpoint occurrence AP and
  an exact period, then finds the overlap cutoff by galloping and bisection in
  candidate rank. Both the period and the candidate count can be huge binary
  integers. This shortcut is integrated through `compressed_lcs.py` after the
  existing successful short-period and sparse-marker shortcuts. Structural
  failure retains the complete matcher; resource interruption propagates.
- `fastunknot/regular_cover_gluing.py` compares supplied assemblies of connected
  regular cyclic or dihedral covers, with coherent whole-boundary attachments
  and optional point or boundary-lift marks. It represents all isomorphisms by
  at most two root congruence classes per graph component. It also provides
  independent transport checking, family verification, canonical unmarked
  keys, and exact phase-orbit counts. It is not wired into the knot-verdict
  pipeline.
- `fastunknot/normal_disk_certificate.py` validates the supplied finite
  triangulation, admissible coordinates, primitivity, modular support rank,
  Euler characteristic, and essential boundary parity. Acceptance certifies
  an essential disk in that triangulation. It does not establish correspondence
  with an input knot diagram and is not wired into the knot-verdict pipeline.

The integration run also identified and corrected an existing subprocess
communication issue in `normal_surface.py`: a large pending input could stop
being written after a timed `communicate()` retry on the tested Python runtime.
The fix uses one public `communicate(payload)` call with cooperative foreground
deadline checks and child cleanup. This is a compatibility correction, not
one of the mathematical advances or a claimed recognition speedup.

## Measured outcomes

Under the fixed 2,000,000-work allowance, the compressed-overlap baseline
completed 13/27 stress cases and the final variant completed 25/27. LCS and
relator-operation cases changed from 10/15 to 13/15 completed. Large
phase-shifted cases remain unresolved within that allowance.

All 15 complete PD-diagram runs had identical certificate digests and search
statistics, with zero endpoint shortcut activations. These runs demonstrate
no end-to-end recognition gain. The article reports this result explicitly.

The regular-cover audit includes 3,480 literal comparisons and exhaustive
checking of 455 small phase assignments. The largest arithmetic benchmark
uses a 24,007-bit modulus. Its tree case encodes `2**23999` compatible maps in
one family. The exact cyclic state count `m**beta` explains why fast
equivalence testing does not bound the number of distinct states.

The normal-disk family has `F_(t+5)-5` elementary normal disks but a small
binary vector. At 128 tetrahedra the vector represents
`2791715456571051233611642548` elementary disks and verifies in a median
9.778 ms in the recorded environment. The largest saved fixture has 256
tetrahedra. Native comparison failures at 22 tetrahedra are recorded as memory
failures under the experiment's limit, never as completed timings.

## Provenance and integration

The patch is based on the public checkout:

```
1be2abc8cc743c1a3b5cb7fdfeb650697f8e2d5b
```

The preceding relevant subtree revision is:

```
38e65c9c2e2bfd42b9f71f1a1a7af15a3f8a3005
```

Both references have the same `fast/` tree:

```
e7222244bb0d7f35cf7f34f83228b350240e4d13
```

From a ProveIt checkout at that baseline, apply the release-root patch with:

```bash
git apply --check /path/to/unknot_research_20261008/integration.patch
git apply /path/to/unknot_research_20261008/integration.patch
```

The patch includes new research material and the precise source/test changes.
The archive also carries a runnable source snapshot in repository-relative
paths, so the research can be inspected without applying the patch. Existing
historical test oracles are preserved under `reports/24/reference`,
`reports/26/detshadow`, and `reports/28/src/closure_reset`; they are unchanged
baseline files and are not added again by the integration patch.

`INTEGRATION_NOTES.md` describes the exact public APIs, failure semantics,
and remaining diagram-to-triangulation and hierarchy extraction obligations.
No remote repository changes are made by this release.

## Reproduce the test suite

The core Python package has no mandatory third-party dependencies. The normal
surface backend and native cross-checks use the optional Regina dependency.
Python 3.12.14 with Regina distribution 7.4.1 was used for the recorded run.
From the repository or extracted release root:

```bash
cd Topology/UnknotRecognition/fast
python3 -m pip install -e '.[normal]'
python3 -m unittest discover -s tests -v
```

Without Regina, native-specific tests skip; the new disk verifier itself does
not depend on Regina. The final full-suite log and the initial diagnostic log
are in the research directory's `verification/` folder. The initial attempt
exposed missing files in the sparse checkout and the pending-input regression;
the final log is the release verification result.

## Verify saved evidence without rerunning timings

From the repository or extracted release root:

```bash
python3 Topology/UnknotRecognition/research/20261008_compressed_certificates/verify_saved_evidence.py
```

This checks the archived source digests, saved disk certificates and exact
Fibonacci counts, recorded completion counts, and knot-certificate/statistic
agreement. It uses the Python standard library and included modules only.
At the release root, `python3 verify_release.py` verifies the SHA-256 manifest.

## Reproduce the measurements

Run these commands from `Topology/UnknotRecognition/fast`. Choose new output
paths when retaining the original measurements for comparison.

```bash
python3 benchmark_compressed_endpoint.py --output /tmp/endpoint_rank_rerun.json
python3 benchmark_endpoint_lcp_ablation.py --output /tmp/endpoint_lcp_rerun.json
python3 regular_cover_research/reproduce.py --output /tmp/regular_cover_rerun.json
python3 -m certificate_research.benchmark --output /tmp/normal_disk_rerun --native
```

The native disk comparator uses Unix process resource limits. Omit `--native`
to regenerate and verify the certificate fixtures without that comparator or
Regina. The endpoint harness includes five measured shuffled rounds after a
warmup and the 15-knot corpus; it can take several minutes. The LCP ablation
helper is the supported entry point; its historical harness is archived with
its original path assumptions for provenance.

The new raw data are:

```
fast/results/endpoint_ap_20261008.json
fast/results/endpoint_ap_lcp_ablation_20261008.json
fast/results/regular_cover_gluing_20261008.json
fast/certificate_research/results/normal_disk_benchmark.json
fast/certificate_research/results/layered_torus_*.json
```

LIMIT is incomplete work. The endpoint JSON retains elapsed times to a limit
for diagnostics, but these are not completion-time medians for an algorithmic
speedup. Same-algorithm controls and negative examples are retained. No large
expanded-sheet gluing baseline is invented or extrapolated.

## Build figures and the article

Matplotlib is needed only to regenerate figures; the generated PDF and PNG
figures are already included. A normal TeX Live installation with `latexmk`
and the listed LaTeX packages builds the article.

```bash
cd Topology/UnknotRecognition
python3 research/20261008_compressed_certificates/build_figures.py
python3 research/20261008_compressed_certificates/build_article.py
```

The scientific figures are generated from saved data, with no timing rerun.
They show observed medians or sample ranges, not fitted complexity claims or
confidence intervals. The article credits classical normal-surface,
covering-space, and compressed-string results separately from the implemented
refinements and experiments.

The article builder uses a clean temporary directory, rejects unresolved
references and overfull boxes, and atomically writes the finished PDF and
build record. A direct `latexmk -pdf` invocation on the main TeX file is also
supported. To regenerate the whole review archive from a Git checkout, run
`build_release.py --output-dir /absolute/path/to/output`; it preserves the
current Git index and verifies the patch in an isolated directory.

## Licensing

Included existing source files retain their repository licenses, including
`fast/LICENSE`, the license in `fastunknot/cyclic_garside`, and the historical
report licenses. The new material is prepared for integration under ProveIt's
existing MIT-0 project license, included at the release root.
