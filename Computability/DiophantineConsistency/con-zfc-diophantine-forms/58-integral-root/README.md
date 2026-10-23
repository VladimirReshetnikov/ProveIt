# Integral-root carriers for Con(ZFC)

**Main result:** a fixed integer polynomial in **15 strictly positive unknowns**,
of **exact total degree 24**, with a **90-operation division-free evaluator**.
At the ordinary mathematical proof level of the explicitly inherited native
compiler, ZFC proves that this polynomial has no positive integer zero if and
only if ZFC is syntactically consistent.

Read **[report/report.pdf](report/report.pdf)** for the complete paper and
**[report/report.tex](report/report.tex)** for its editable LaTeX source.
The twelve-variable section is included from `twelve/section.tex`.

## New measured points

| Polynomial | Domain | Unknowns | Exact degree | Binary operations |
|---|---|---:|---:|---:|
| `p15_degree24.json` | Strictly positive integers | 15 | **24** | **90** |
| `p15_degree26.json` | Strictly positive integers | 15 | **26** | **88** |
| `p15_degree30.json` | Strictly positive integers | 15 | **30** | **79** |
| `p12_desaturated_product.json` | Strictly positive integers | 12 | **629** | **114** |

The strongest supplied degree-44 fifteen-positive comparison is the
**75-operation** minimum-norm grouping in source 47. The directly related
source 49 root-gap construction uses 76 operations. Thus the main result
reduces degree **44 → 24 (45.45%)**, with **15** additional gates relative
to the stronger incumbent. Degree 30 provides a **31.82%** reduction for
four additional gates. The twelve-variable comparison is **897/108 → 629/114**.

The main three polynomials are sums of squares. Their residual degrees are:

| Output degree | Residual degrees |
|---:|---|
| 24 | 11, 9, 4, 3, 12, 10 |
| 26 | 11, 9, 7, 13, 10 |
| 30 | 12, 15, 15, 10 |

The degree-24 leading form is

```text
4 X^4 Y^6 f^8 u^2 ((eta+zeta) T + h X)^2.
```

Its coefficient of `X^6 Y^6 f^8 u^2 h^2` is exactly 4, independent of the
fixed numerals. Degree is computed after cancellation, not by naive degree
propagation through the raw evaluator.

## New idea

An existing monic square equation can force a divisibility condition. From

```text
(q^3 (ell+r) + Y)^2 = q^6 (ell(ell+k)+1)
```

one obtains `q^3 | Y`, since a rational square root of an integer is integral.
This permits `Y` to be supplied directly instead of repeatedly substituting
`s q^3`. After that recovery, a second square equation forces `q | X`.
Canonical positive Pell gaps justify both inverse substitutions. Reducing
the auxiliary expression modulo the retained index equation gives the final
degree-26 to degree-24 improvement.

The squared-modulus auxiliary quotient, ordinary Pell-rank theorem, compact
coefficient tuple, and formal-norm evaluator are inherited ingredients and
are credited in the paper. The new work is an existence reduction; it can
choose fresh auxiliary witnesses and is not a same-coordinate identity with
every predecessor witness.

## Fixed coefficient binding

Every new circuit uses the **whole** source-44 compact tuple:

```text
beta = 2^590069 - 1
K0   = DC + B*DR
MC   = native low mask
MF   = MF_native + B - 1       (already shifted)
```

`coefficients/COEFFICIENT_BINDING.json` defines all aliases, file paths,
bit lengths, and compressed/raw SHA-256 digests. The four little-endian
unsigned integer payloads occupy 295,388 raw bytes (9,445 gzip bytes).
They are fixed numerals, not extra unknowns. The coefficient builder and
independent inherited auditor, literal K215 transition table, Wang tile list,
native proof, and notices are included.

The repository comparison is pinned to
`6d375f2d2deac0519e659bbce5b48087023c1430`, including wave-7 material that
arrived through `docs/incoming`. Exact original paths and hashes are in
`PROVENANCE.json`; the twelve-variable subtree has an additional source ledger.
The historical `source_commit` inside the untouched coefficient binding
records that adapter's original starting point, not this review's snapshot.

## Reproduce

Python 3 is sufficient for the arithmetic checks; all new verification code
uses the standard library. From any directory:

```sh
python3 /absolute/path/to/ConZFC_Integral_Root_2026-10-23/verify_all.py
```

The runner rebuilds the circuits, checks byte-identical regeneration, runs
the exact degree/identity verifier, independent direct-formula checks, domain
translations, companion checks, and the inherited coefficient audit. It
writes a deterministic receipt under `certificates/`. The new checks also
run with `python3 -O`; verification conditions use explicit exceptions.

For the paper, use a standard LaTeX installation with the packages named in
the preamble:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

For exact file integrity before rerunning builders:

```sh
sha256sum -c MANIFEST.sha256
```

## Archive layout

| Path | Contents |
|---|---|
| `report/` | Complete paper in PDF and LaTeX |
| `circuits/` | Three main circuits, degree certificates, two domain translations |
| `code/` | Deterministic builders and independent/exact checkers |
| `certificates/` | Receipts, exact leading forms, final verification and PDF checks |
| `coefficients/` | Complete bound numerals, compiler adapter, source data, auditor |
| `twelve/` | Degree-629 companion, two systems, proof, checker, pinned sources |
| `upstream/` | Inherited kernel/Pell proofs, comparisons, K215 status |
| `review/` | Explicitly labeled internal AI-assisted mathematical reviews |

The twelve-variable systems have three equations, maximum residual degree
622, and 109 operations, or 108 with the established positive transport
shift. These system costs are not presented as single-polynomial costs.

## Domain and formalization limits

The compact theorem concerns **positive** integer unknowns. The supplied
`p15_nonnegative_degree24.json` shifts each input by 1 and gives the same
equivalence over `{0,1,2,...}`. The supplied `p60_integer_degree48.json`
uses `1 + four squares` per input and gives an equation over all integers.
These translations are provided for explicit domain handling; the sixty-
integer variant is not a small-variable frontier improvement.

This package provides ordinary mathematical proofs formalizable in ZFC.
It does **not** provide a newly kernel-checked end-to-end formalization or an
object-language ZFC derivation file. The inherited K215 endpoint already has
reported Lean and Rocq proofs; those builds were not rerun here. The native
Diophantine compiler and the complete new reductions retain the proof boundary
described in the paper and the bundled source documents.

The reviews are internal AI-assisted reviews, not external peer review.
Finite checks certify exact identities, transcription, degree, constants,
and provenance; they cannot decide whether the equation has a positive zero.
No consistency assumption is used, no refutation search is performed, and
no global minimum or new operation-count record is claimed.

## Attribution and integration

Prepared for Vladimir Reshetnikov as a proposed ProveIt research contribution.
New material follows the repository's MIT No Attribution license. Copied
upstream files retain their own notices and licenses; see `NOTICE.md`.
No repository changes were published as part of preparing this archive.
