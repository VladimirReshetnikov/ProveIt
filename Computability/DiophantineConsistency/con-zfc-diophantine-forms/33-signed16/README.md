# Explicit Con(ZFC) equations: sixteen integers and simpler presentations

This release supplies an explicitly specified polynomial in **16 unrestricted
integer variables** whose absence of integer zeros is provably equivalent in
ZFC to Con(ZFC). It also supplies independent improvements to positive-variable
presentations and to the native compiler's fixed coefficients.

Read **[report.pdf](report.pdf)** for the mathematical article, or build it from
**[report.tex](report.tex)**. All mathematical claims are ordinary proofs with
the inherited compiler and machine-calibration dependencies explicitly stated.
There is no new end-to-end Lean or Rocq certificate and no proof of Con(ZFC).

## Results

The baseline is the repository at revision
`8c6eec9d19ef80538c8e61ff6e0180040583446a`, particularly packages 27, 29 and 30.

| Presentation | Domain | Degree | Delivered cost | Improvement |
|---|---|---:|---:|---|
| One signed16 equation | 16 unrestricted integers | `406528*5^32+10008` | 1,590 operations | 17 to 16 unknowns; lower degree and circuit cost |
| 22-equation system | 31 positive integers | 2 | 61 operations | 65 to 61 |
| Quartic sum of squares | 31 positive integers | 4 | 126 operations | 130 to 126; 306 to 259 symbolic monomials |
| Identical degree-1081 polynomial | 12 positive integers | 1081 | 108 operations | 111 to 108 |
| Associated three-equation system | 12 positive integers | 1072 maximum | 104 operations | 107 to 104 |
| Shifted three-equation system | 12 positive integers | 1072 maximum | 103 operations | One further justified affine shift |
| Optional complete coefficient tuple | Fixed constants | — | `B=2^1012625` | 48.1536% smaller exponent than the previous smallest `B=2^1953125` |

Operations are live binary additions, subtractions and multiplications, including
scalar multiplication and squares. Reuse and system-side comparisons are free.
Fixed integer coefficients are leaves, not witnesses. Costs are arithmetic-circuit
sizes, not bit-complexity claims. All auxiliary names in the paper are polynomial
abbreviations unless they appear in the declared variable list.

The natural-variable record, the repository's 67-operation equation and its
59-operation systems are not improved by this release. Sun's general 2026
ten-integer representation theorem also gives a better general variable bound;
that compiler is not instantiated here. No global minimality or priority claim
is made.

## Main construction

The 16 variables are

```text
epsilon, g, h, s, w, phi, i, j,
z1, z2, z3, z4, z5, z6, residue, normroot.
```

The proof combines the selected affine quartic with the literal Jones ratio
construction, six guarded Pell factors, a degree-five intersective polynomial,
and a three-radical norm. A new normalization lemma makes the signed `j`
coordinate positive within its residue class, saving one witness. A second
improvement uses the unconditional congruence `Cguard6 == 1 (mod 4)` to replace
a quadratic separating weight by the linear weight `Cguard6+1`.

The final polynomial is specified exactly by its topologically ordered integer
arithmetic circuit in [data/signed16.json](data/signed16.json). The finalizer is

```text
X = S*normroot - T
A0 = S^2*Cguard6
A1 = (S*weight1)^2*a0
A2 = (S*weight2)^2*a1
V = X^2 + A2 - A0 - A1
W = V^2 + 4*X^2*A2 - 4*A0*A1
P16 = W^2 - 16*V^2*X^2*A2.
```

The paper and circuit give every abbreviation. The coefficient recipes in
[data/coefficients31.json](data/coefficients31.json) are finite arithmetic
definitions; they do not query consistency or introduce extra unknowns. The
huge fixed Jones index is intentionally given by a bounded sum, rather than
an infeasibly long decimal expansion.

## Coefficient binding

The main signed16, quartic31 and positive12 objects all retain the **same
complete package-30 tuple**. Its authoritative binding is
[upstream/compiler/binding.json](upstream/compiler/binding.json). Four compressed
binary files contain the actual fixed integers. Decompression yields a
minimal-width unsigned little-endian integer with no header. The fourth
coefficient is `MF_source = MF_native + B - 1`; it is already shifted.

[coefficients_small/](coefficients_small/) provides a **different complete
tuple**, with a separate proof and all four actual integer payloads. Its
base exponent is 1,012,625 and its largest coefficient has 1,015,251 bits.
The four integers occupy 506,644 raw bytes, or 10,502 gzip bytes in this release.
This tuple is not silently substituted into the main fixed equation. To use it
in a compatible direct form, bind all four ports together. To use it in the
Jones reduction, regenerate the weighted coefficient recipes and index bound
for that complete tuple first. See its [proof](coefficients_small/PROOF.md)
and [independent review](coefficients_small/EXTERNAL_REVIEW.md).

## Reproduction

Extract the complete archive, then run:

```sh
python3 reproduce.py --check-release
python3 reproduce.py
```

The first command authenticates the distributed files. The second rebuilds
all new circuits, coefficient recipes and the optional tuple, and runs all
eight check stages. It requires **Python 3.10 or newer and only the standard
library**, without network access or a checkout of the rest of ProveIt. It may
be launched from any working directory. Do not use `-O`: some independent
audits intentionally use assertions. `--verbose` prints the full receipts.

To rebuild the PDF, use a TeX installation containing the packages named at
the top of `report.tex`, then run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

`make all` performs both tasks. PDF bytes can vary with the TeX installation
and timestamps. Compression bytes can vary with the zlib version; the raw
integer bytes and their hashes are the mathematical coefficient identity.

## What the checks establish

- All 22 affine residual identities are checked exactly with symbolic ports.
- The shifted quartic is independently expanded from its quadratic residuals;
  all 391 weighted coefficient records and the strict fixed-index bounds agree.
- The eight-factor radical norm is checked as an exact polynomial identity.
- The delivered signed16 circuit is compared with direct formulas and literal
  58,905-term digit sums at actual-instance modular residues.
- All source snapshots and the four main integer payloads are authenticated.
- The 12-variable circuit is compared with the predecessor and an independent
  eight-component conjugate-product evaluator.
- The optional tuple has two separately implemented arithmetic audits,
  including 69,230 native-basis identities, carry and population checks, and
  constructive Boolean rank-control examples.

These checks accompany the universal mathematical proofs. Finite tests are
not used to decide consistency, certify a nonhalting computation, or replace
the inherited native compiler's unbounded theorem. The semantic dependency
boundary is explained in Sections 2 and 13 of the paper and in the subpackage
proofs. See [verification/](verification/) for the receipts.

## Contents and integration

| Path | Purpose |
|---|---|
| `report.tex`, `report.pdf` | Complete article and rendered version |
| `reproduce.py`, `Makefile` | Portable regeneration and checking |
| `code/` | Main index builder, signed16 builder and independent verifier |
| `data/` | Fixed recipes, strict index certificate and signed16 circuit |
| `quartic31/` | Affine quadratic system, quartic, exact symbolic verifier and proof |
| `positive12/` | Refactored 108/104/103-operation objects, proof and verifier |
| `coefficients_small/` | Separate smaller complete tuple, construction and two audits |
| `upstream/` | Pinned source excerpts, compiler data and actual main coefficients |
| `verification/` | Build, arithmetic and review receipts |
| `SOURCE_MANIFEST.json` | Original repository paths, commit and source hashes |
| `RELEASE_SHA256.json` | Hashes of the delivered files |
| `licenses/` | Retained upstream licence and machine-source notices |

Keep this directory together when incorporating it in the repository: active
scripts refer to included files by paths relative to their own locations.
Source scripts under `upstream/` are retained reference material, not standalone
entry points. The active entry point is `reproduce.py`. The bundled Lean files
are source endpoints for attribution and inspection; they are not a standalone
Lean project. [INTEGRATION.md](INTEGRATION.md) provides a suggested index entry.

Prepared 22 October 2026, with AI-assisted mathematical analysis and independent
agent reviews. The new proofs and checks remain open to human review. Original
K215, native compiler, Pell, Jones and norm constructions are credited to the
pinned ProveIt sources and the references in the paper.
