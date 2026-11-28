# Collapse the initial gauge average

## Recommendation

Replace the first-path symmetrization by its normalized character-valued orbit section. The exact residual stabilizer is a product of false interior congruence kernels. Its cardinality is independent of the twist. The normalized initial coefficient is always zero or one root of unity, so its coefficient budget is **1**.

The first-column period normalization simultaneously collapses from a product of all intermediate GL ratios to the endpoint ratio `d0 / h0`. The report checks why this does not reintroduce the initial coefficient factor through the final free scalar. A complementary proposal replaces root-multiset certificates by universal integrality and a size bound only at the trivial twist, using one terminal finite expansion.

The known fixed sweep, exact diagonal Fourier budget, active-frontier representation, sharper terminal count, and removal of the unused true initial-node slot are **excluded as existing proposals**. The new theorem evaluates all the remaining averaging fibres after that slot is removed.

## Start here

- `report.pdf`: complete mathematical proposal, proofs, source links, implementation sequence, and verification limits.
- `report.tex`, `preamble.tex`: editable LaTeX source.
- `formal/OrbitCharacterSum.lean`: **uncompiled** proposed Lean proofs for the elementary finite-character/torsor component only.
- `checks/`: exact Python finite models, source and proposal integrity checkers, and recorded outputs.
- `audit/`: pinned manifests and the full non-duplication review.
- `review/`: detailed derivation, independent stabilizer review, adversarial scalar review, and arithmetic-contract analysis.
- `SHA256SUMS`: SHA-256 digests of the delivered files, excluding the digest file itself.

## Source snapshot and scope

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Pinned commit: `1a59f50680e470fb5269bbe70c06f974c95ad930`.

The core proposal audit covers 26 directories and 79 non-attribution Markdown/LaTeX texts. It also excludes the removed `robust_theta_labels` proposal as previously reviewed work. A late update to the repository added existing sweep proposals, so an earlier sweep candidate was discarded and is not the recommendation delivered here.

A supplemental audit at `0ae2eb38ee385fa1a22fb36bb5ad65d909a259b1` reviews the two later directories `grh_frobenius_jet_simplification` and `grh_simplification`: 20 additional non-license TEX/MD/TXT texts, 236,109 bytes. Their proposals are excluded too. All 79 earlier proposal texts and all auxiliary-form source files are unchanged at that supplemental cutoff; other source files changed. The core source manifest remains pinned to `1a59f50680e470fb5269bbe70c06f974c95ad930`.

The exported GRH statements inspected are for Dirichlet characters. This work is a source-derived simplification proposal, **not an independent certification of the complete RH/GRH proof**.

## Reproduce

Python 3.10 or later is sufficient for all checks. Git is needed for the optional source audits. Building the PDF requires `pdflatex` with Latin Modern, AMS packages, microtype, geometry, booktabs, tabularx, longtable, needspace, xcolor, enumitem, fancyhdr, tikz, hyperref, xurl, bookmark, and listings.

From this directory:

```bash
python3 build.py
```

This reruns the exact finite gauge models and compiles the PDF three times. It stops on LaTeX errors, overfull boxes, unresolved references, or remaining LaTeX warnings. Build intermediates go in `.build/`.

For the checks without rebuilding the PDF:

```bash
python3 build.py --skip-pdf
```

With an existing ProveIt checkout at the pinned commit and the full relevant `src/New` and `docs/proposals` trees present:

```bash
python3 build.py --repo /absolute/path/to/ProveIt
```

The script reads the checkout and never changes it. It validates 27 source-file hashes, 116 declaration anchors, source occurrence counts, and all 79 proposal text hashes. A later `main` checkout will correctly fail the snapshot check: check out the recorded commit separately to reproduce this audit.

If the same repository also contains Git objects for the supplemental cutoff `0ae2eb38ee385fa1a22fb36bb5ad65d909a259b1`, add `--supplemental` to verify the 20 later texts, the unchanged 79 earlier texts, and the unchanged auxiliary-form tree. This reads the later objects without checking out that revision:

```bash
python3 build.py --repo /absolute/path/to/ProveIt --supplemental --skip-pdf
```

To check the delivered archive contents before regenerating outputs:

```bash
sha256sum -c SHA256SUMS
```

## Verification status

The exact finite checker passes five coupled two-chain models, enumerating 60,288 gauges and 30,144 orbit fibres. It performs 422,016 direct transporter-predicate checks, 9,216 noncommutative GL-character multiplicativity checks, and ten off-orbit controls. The model includes rectangular split inclusions and an off-orbit tuple whose individual edges are all split-injective.

These finite checks test the mechanism and catch orientation, endpoint, cancellation, and normalization mistakes. The report supplies the general argument; the tests do not prove the all-modulus statement or any analytic theorem.

No Lean/lake executable was available. The supplied Lean file has no admitted placeholders but has not been parsed, elaborated, or kernel-checked. It does not contain the source-specific gauge action, stabilizer identification, CRT bridge, or integrated replacement. Net line savings and build-time savings have not been measured.

The normalized coefficients are integral at every prime. The final terminal-period denominator theorem retains the source's original exclusion of primes dividing the twist norm. Divisibility by the removed multiplicity adds no exception among the primes allowed by that theorem.

The PDF was compiled and visually checked. No modifications to the upstream repository were made.
