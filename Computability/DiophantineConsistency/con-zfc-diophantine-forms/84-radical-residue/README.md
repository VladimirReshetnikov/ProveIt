# Ten-variable Diophantine consistency by small rational residues

Prepared for Vladimir Reshetnikov, 23 October 2026. Repository snapshot:
`c1a102936aca437e9999530a0111e6ddab56dc6d`.

## Results

The principal new equation has **10 strictly positive integer variables,
exact total degree 1152, and 131 live binary arithmetic operations**.
For its explicitly bound compact44 coefficient tuple, the ordinary proof
composed with the inherited native compiler and refutation-calibration
theorem establishes, in ZFC,

> The equation has no positive integer solution if and only if Con(ZFC).

Its nonnegative-integer translation has 10 variables, degree 1152, and
141 operations. The translation is exactly `x = x0 + 1` in every coordinate.

Separate unrestricted-integer constructions use the source34 tuple:

| Packet | Variables | Exact degree | Binary operations |
|---|---:|---:|---:|
| `integer/forms/norm17_degree112.json` | 17 | 112 | 124 |
| `integer/forms/norm17_degree110.json` | 17 | 110 | 140 |
| `integer/forms/center18_degree80.json` | 18 | 80 | 115 |
| `integer/forms/pivot18_degree88.json` | 18 | 88 | Not measured |
| `integer/forms/pivot19_degree32.json` | 19 | 32 | Not measured |
| `integer/forms/pivot20_degree20.json` | 20 | 20 | Not measured |
| `integer/forms/pivot21_degree16.json` | 21 | 16 | Not measured |

An operation is one live binary addition, subtraction, or multiplication,
including squaring and multiplication by a fixed scalar. Numeral leaves
and reuse of registers are free. This is not bit complexity. No global
minimum over all possible equations or circuits is asserted.

## What is new

The positive construction merges four root witnesses into one coordinate.
The critical step recovers Pell indices before resolving the carrier
congruences. Pell growth then bounds an integral rational residue in
absolute value by one, forcing it to vanish and recovering the desired
power and root sign. The argument does not require the generally false
coprimality of the two carrier moduli, and it introduces no extra
divisibility condition on the canonical witnesses.

The integer construction scales one of two roots by an existing integer
whose square occurs in the adjacent-coefficient Pell equation. Equality
of the two radicands becomes impossible modulo that square. Rational
root recovery followed by Pell descent restores genuine integer roots.
A centered coordinate lowers the degree; a further polynomial shear gives
the degree-110 alternative.

These are improvements relative to the inspected ProveIt snapshot and
incoming archives. The four-root separation principle, transport pivot,
positivity guards, and native consistency calibration are credited to
their existing sources. Independent AI-agent review is not external human
peer review. The archive does not claim a new end-to-end Lean/Rocq proof
or an explicit object-language ZFC derivation.

## Read first

- `report.pdf`: the complete research report, equations, proofs, comparison,
  coefficient definitions, and formalization boundary.
- `report.tex`: standalone LaTeX source; it has no missing input files.
- `ten_positive/PROOF.md`: detailed positive-domain proof.
- `ten_positive/INDEPENDENT_MATHEMATICAL_REVIEW.md`: independent proof audit.
- `integer/PROOF.md`: all integer-domain reductions and degree certificates.
- `audit/README.md` and `audit/audit_summary.json`: incoming-source audit.

The main literal arithmetic graphs are
`ten_positive/generated/p10_positive.json` and `p10_natural.json`.
Every named register is an abbreviation, not an additional quantified
variable. The integer `forms/` folder contains fully inlined residual
expressions and three separately counted arithmetic DAGs.

## Fixed coefficients

The positive equation uses four fixed compact44 integers, with
`beta = 2^590069 - 1`. Their actual unsigned little-endian bytes occupy
295,388 bytes before gzip. The supplied recipe reconstructs them from the
literal 430-action machine table, without running the machine.

The integer family uses six source34 integers, with
`beta = 2^1064921 - 1`, together with the determinant scales
`2^1113` and `2^666104`. Their raw payloads occupy 615,883 bytes.
The two coefficient tuples must not be interchanged. In both families,
the `MF` port is already shifted as specified by its source.

Every payload is present under the corresponding `coefficients/` folder.
`BINDING.json` records its exact interpretation and hashes. Upstream file
identities, immutable repository URLs, and licenses are retained.

## Reproduce the checks

Python 3.10 or later is recommended. The principal independent checks and
the complete positive coefficient reconstruction use only the standard
library:

```sh
python3 verify_all.py
```

This checks archive integrity when a manifest is present, the positive
builder's exact output, the natural-coordinate translation, the sixteen-
factor norm identity, all 62 named arithmetic cuts, topology, liveness,
operation counts, exact degree, fixed coefficient bytes, local negative
controls, inherited source hashes, and the independent 17/112, 17/110,
and 18/80 integer certificates. It writes `VERIFICATION_LAST_RUN.json`,
preserving the delivered `VERIFICATION.json` receipt and checksum manifest.

For the additional SymPy-based verifier covering every integer packet
and all three integer DAGs:

```sh
python3 -m pip install -r integer/requirements.txt
python3 verify_all.py --symbolic
```

The delivered `integer/certificates/VERIFY.json` and
`VERIFY_OPTIMIZED.json` record successful normal and `python3 -O` runs.
The independent checkers use explicit failure checks, not removable
Python `assert` statements. Exact polynomial identities and leading-term
certificates are distinguished from finite modular diagnostics in their
receipts. None of these programs searches for or tests the consistency
of ZFC.

To regenerate equation files, run:

```sh
python3 ten_positive/build.py
python3 integer/build.py
python3 integer/circuit.py
```

To rebuild the PDF, run twice from this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The supplied report was rendered and visually inspected. Its mathematical
proofs supply the unbounded arguments; finite code checks do not replace
the Pell or native compiler proofs.

## Incorporation

This directory can be added as one research package under the repository's
Diophantine forms collection. The files are self-contained for defining
and checking the supplied equations; the historical semantic calibration
remains a named mathematical dependency, with key source proofs bundled.
No existing repository files were modified. `MANIFEST.sha256` authenticates
the delivered files; regeneration may change the manifest's expected
bytes. See `NOTICE.md` and retained licenses for provenance.
