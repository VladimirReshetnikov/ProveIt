# Beyond Dirichlet GRH

**Averaged zero detection and exact K-theory transfer tests**  
Prepared for Vladimir Reshetnikov, 25 November 2026 (Pacific date).

Read **report.pdf** for the complete report. The main source is **report.tex**,
with chapter files under **sections/**.

## Results and scope

This investigation analyzes the arithmetic methods inside `lsernau/grh-lean`,
builds on all eleven supplied ProveIt reports, and adds:

1. A positive-part Mellin criterion that replaces a pointwise upper bound by
   weighted positive-part integrability, with dyadic L1 and L2 sufficient
   conditions and a complete proof.
2. A signed moving-interval criterion, its zero-free Mellin multiplier, and
   explicit counterexamples to sparse signed sampling and general positive
   smoothing.
3. A mean criterion for combined rank, index and denominator losses, and its
   precise application to the conductor-23 nonabelian cubic benchmark.
4. Exact Bernoulli-unit screening for possible K-theory extensions to degrees
   124 and 128, with a table through degree 160; two independent rational
   constructions and fourteen Bezout certificates.
5. Exact dimensions of the proposed next comparison spaces, and two small
   Hecke operators independently regenerated from the published neighbor
   formula.
6. A source-level distinction between the short proof's odd-cocycle bound and
   the stronger ordinary strict-Selmer interface used in the existing
   K-theory papers.

**No new nonabelian RH instance or K-group vanishing theorem is claimed.**
The averaged estimates for the actual cubic prime remainder, and the full
strict-Selmer-to-Hecke bridge and large determinants for the next K-theory
degrees, remain to be established. The analytic principles adapt classical
Landau theory; no literature-priority claim is made for the finite identities.

## Reproduction

Use Python 3.10 or later. The two exact K-theory programs use the standard
library. The symbolic and plotting programs additionally require SymPy,
NumPy and Matplotlib (listed in `requirements.txt`).

```bash
python3 reproduce.py
```

This reruns all original computations, including the orbit-count ranks, and
writes their results and logs under `checks/`. It does not download sources,
rerun external large certificates, or compile Lean.

To rebuild the PDF as well:

```bash
python3 reproduce.py --pdf
```

The driver uses `latexmk` with TeX Live, or Tectonic as a fallback. When the
installed TeX Live sources are present but the pdfLaTeX format is missing,
`code/build_pdf.py` can generate a temporary format locally. The LaTeX source
uses standard packages. This delivered PDF was compiled with pdfLaTeX and
rendered for visual inspection.

Individual commands:

```bash
python3 code/verify_ktheory_prefilter.py --ranks --output checks/prefilter_results.json
python3 code/verify_ktheory_small.py --output checks/small_reconstruction_results.json
python3 code/check_mean_transfer.py
python3 code/mean_models.py
```

An optional static inventory of an independently obtained upstream checkout:

```bash
python3 code/audit_source.py /absolute/path/to/grh-lean
```

That checkout must be at `72fead102f663d5c7a407964a13dc0cf9d977207`.
This checks source hashes, the presence of local imports, specified lexical
tokens outside comments/strings, and identical statement files. It is not a
Lean build or kernel replay. The complete upstream repository is not bundled.

## Evidence and provenance

- `evidence/prior_archive_manifest.json`: immutable paths, Git blob identities
  and SHA-256 hashes for the eleven previous reports and their incoming README.
- `evidence/prior_report_audit.txt`: a filename-by-filename overlap audit. Its
  descriptions of previous classifications remain attributed claims unless
  specifically marked as independently checked.
- `evidence/source_inventory.json`: hashes of all 1,597 Lean source files in
  both upstream editions, with static-check results.
- `evidence/source_provenance.json`: selected original-source paths and hashes,
  fixed revisions, and primary verification references.
- `evidence/upstream_stored_coverage_manifest.json` and its run log: exact
  scope and provenance of the replay of Pintar's stored large certificates.
  The external checker and its two certificate ZIPs are identified by hashes
  and immutable URLs, and are not bundled here.
- `evidence/upstream_small_replay.log`: the original small two-probe script's
  results, distinct from our standalone one-probe matrix reconstruction.
- `checks/`: new rational, symbolic and combinatorial results and run logs.
- `figures/averaged_spikes.pdf` and `.png`: synthetic mathematical illustration,
  not prime data or numerical evidence for a new RH case.
- `source_excerpt/`: selected Apache-2.0 upstream files, with their license,
  notice and attribution. They serve as auditable source anchors; they are not
  a self-contained Lean project.

To validate the distributed files before rerunning scripts:

```bash
sha256sum -c SHA256SUMS
```

Rerunning the programs may update logs, environment metadata and figure/PDF
metadata even when the mathematical outputs are unchanged.

## Verification boundary

All original arithmetic programs were run successfully. The Bernoulli screen
performs 84 rational-value comparisons, including repeated values at index
zero, and checks fourteen Bezout identities. The rank calculation evaluates
eight dimension/trace triples. The small reconstruction uses exact arithmetic
in Q(sqrt(-3)), checks eighteen neighbor matrices and six incidence pairs,
and reconstructs the operators at e=6 and e=8 without reading stored matrices.

The large upstream replay checks stored arithmetic records. It does not
reconstruct the large matrices. Neither that replay nor our source inventory
replaces a proof of the cohomological bridge. No full Lean build or kernel
replay, and no new Lean formalization of the report's analytic theorems, was
performed in this investigation. The external independent Lean verification
record is cited separately in the report.

## Fixed source revisions

| Source | Revision |
|---|---|
| lsernau/grh-lean | `72fead102f663d5c7a407964a13dc0cf9d977207` |
| VladimirReshetnikov/ProveIt | `b65aa6229415bdb66d9ce52decc4e997793cd07d` |
| CocoSgt/riemann-hypothesis-lean | `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4` |
| leopintar05/hecke-k-theory-104, v1.0 | `5c876949ccba300dbf580f7b3bbfd0e511856faf` |
| Pintar coverage checker and text | `f00206f900a6cb3ae7ebf8cf3ce0d51dffb8cc03` |
