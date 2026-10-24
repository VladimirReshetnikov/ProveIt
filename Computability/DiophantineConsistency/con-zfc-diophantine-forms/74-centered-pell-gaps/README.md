# Centered Pell gaps and adaptive congruence moduli

Research contribution for Vladimir Reshetnikov's ProveIt project, 23 October 2026.
Comparison snapshot: `a2cd79b9120fc75f48dcbef6e38d0f8b18d64d49` (sources 60–67 included).

## Proved improvements

| Equation | Domain | Unknowns | Exact degree | Live binary operations | Direct source-61 baseline |
|---|---|---:|---:|---:|---|
| `circuits/positive12_product.json` | Positive integers | 12 | **110** | **100** | Degree 118 / 104 operations |
| `positive13/p13_degree30.json` | Positive integers | 13 | **30** | **93** | Degree 34 / 93 operations |
| `circuits/positive12_sos.json` | Positive integers | 12 | **164** | **99** | Degree 172 / 103 operations |

Each is one fixed integer polynomial. Its lack of solutions on the indicated
domain is equivalent to `Con(ZFC)` by ordinary mathematical proofs formalizable
in ZFC, composed with the explicitly named inherited native compiler and
K215/refutation calibration. No new end-to-end Lean/Rocq certificate is claimed.
The source theorem dependencies are retained; the new reductions, positivity,
exceptional cases, and degree proofs are given in full in `report.pdf` and
`report.tex`.

This is an improvement at the twelve- and thirteen-positive-variable slices.
It is not a global minimum, a new fewest-variable result, or a wholly new
consistency encoding. The nine-positive frontier, ten-integer frontier, and
lower-degree equations with more unknowns remain distinct alternatives.
Source 62 also retains a cheaper 13-positive / degree-114 / 83-operation point.

## Two ideas

1. After recovering `q^3 | Y`, use the adaptive carrier modulus `U=q^2 Y`
   and offset coefficient `L=qY`, replacing `q^5` and `q^4`. Its possible
   common factor three is removed from a cofactor of `Y`, so the remaining
   modulus is still at least `q^4`. This is why the recovery order matters.
2. Merge the strong Pell root and auxiliary gap into one coordinate and
   center the strong root at `(a+2) I` before taking the norm. The exact
   error is `1-I^2`, of degree 10 instead of 14. The apparent zero-denominator
   branch is algebraically impossible, and a canonical Pell gap proves that
   the new coordinate is positive.

The general adaptive-modulus and root-centering strategies already occur in
sources 64–65 and 62, respectively. The contributions here are the precise
new combination, the strong-root center, and their proved quantitative effect.

## Exact fixed coefficients

All new equations use **the complete compact44 tuple**. The four actual fixed
numerals are in `coefficients/`, occupying 295,388 decompressed bytes in total.
The `K` payload binds to `K0`; `MF_source` binds to `MF` and is already shifted.
The payloads and their finite reconstruction recipe are included. They do not
depend on whether ZFC is consistent. Coefficient height is unchanged.

## Reproduction

Only the Python standard library is needed:

```sh
python3 verify.py
```

The verifier regenerates every new circuit in a temporary directory, reconstructs
all four numerals from the literal transition table and finite compiler recipe,
checks source hashes, runs independent exact algebra/degree checks, and records
scope-labeled diagnostics. It does not search for zeros or prove consistency.

Compile the standalone main article twice:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Files under `upstream/` are retained evidence and source recipes; the main report
does not need to compile those historical LaTeX sources. The historical binding
lists its original relative `coefficients/` prefix; the four payloads now sit
beside the binding, and `evaluate.py` and `verify.py` resolve this explicitly.

`evaluate.py` evaluates a selected graph at supplied inputs, optionally modulo an
integer. Intermediate registers are abbreviations, never additional witnesses.

## Domain companions

`circuits/natural12.json` shifts all inputs by one: 12 nonnegative unknowns,
degree 110, 112 operations. `circuits/integer36.json` substitutes
`1+a^2+b^2+c(c+1)` for every positive input: 36 unrestricted integer unknowns,
degree 220, 184 operations. The standard three-square argument establishing
surjectivity is in the report. These companions remove domain ambiguity; the
36-integer equation is not a new unrestricted-integer frontier point.

## Integration

Place this package beside the existing research contributions. Retain the other
domain/degree/cost tradeoffs. `upstream/FETCH_LEDGER.json` pins retained source
bytes and Git blobs. `VERIFICATION.json` states exactly what the finite checks
establish. `MANIFEST.sha256` authenticates the release files.

The mathematical reviews were produced by separate AI-assisted workers in this
research session, not external human peer review. No remote repository mutation
is part of this delivery.
