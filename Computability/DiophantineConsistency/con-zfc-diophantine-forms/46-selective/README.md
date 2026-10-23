# Selective coefficient extraction for explicit ZFC consistency equations

Prepared for Vladimir Reshetnikov's ProveIt project, 23 October 2026.

Reviewed repository snapshot:
`124c07c0b77a9e20e84676514d8b1ff78536ea3f`, including the placed wave-6
packages 38–45 and the active short-circuit research. The original incoming
directory is a placement ledger at this snapshot.

## Main results

The fixed polynomials defined here satisfy, by the ordinary arithmetic proofs
and explicitly identified inherited theorems in `report.pdf`,

> There is no zero in the stated witness domain if and only if Con(ZFC).

This equivalence has a proof formalizable in ZFC; it assumes neither
consistency nor inconsistency. The work does not decide either side.

| Polynomial | Witness domain | Exact total degree | Live binary operations |
|---|---|---:|---:|
| `data/polynomial.json` | 10 unrestricted integers | **35,876,184** | **640** |
| `nine/generated/selective_nine_positive.json` | 9 positive integers | **19,615,180** | **606** |
| `nine/generated/selective_nine_natural.json` | 9 nonnegative integers | **19,615,180** | **609** |

The ten-integer baseline in package 40 has degree 237,520,456 and 782
operations. The new degree is 6.62056 times smaller, with 142 fewer
operations. The nine-positive baseline in package 45 has degree 129,875,980
and 788 operations; the new construction has approximately 84.9% smaller
degree and 23.1% fewer operations.

The count charges each live binary addition, subtraction, and multiplication
once. Reuse and fixed coefficient leaves are free; fixed powers are expanded
into multiplications. This is arithmetic-circuit size, not bit complexity or
the size of a printed expanded polynomial. The main ten-integer count is
422 multiplications, 138 additions, and 80 subtractions.

### The new construction

The positive quadratic parent has 31 unknowns and 22 equations, but its
unshifted support uses only 62 of the 528 possible padded quadratic
monomials. The explicit weight list of maximum 175 isolates each of these
62 monomials against **all** 528 pairs. Unused pair sums may collide.

A single shared word `1 + ell + g`, with `ell = sum B^w_i`, turns
nonnegative packed digits into positive parent coordinates. This avoids
expanding the positivity shifts in every equation. The reversed kernel
then has 94 coefficient records and nine nonliteral coefficient recipes.

Nonuniform targets chosen for the actual supports, followed by a common
translation of -104, yield maximum target 5148 and product span 5498.
The exact extraction identity is proved symbolically for all 22 rows,
with all four coefficient ports left indeterminate. The new source is
composed separately with the inherited Sun and Jones arithmetic bridges.

### Explicit coefficients

The main equations keep the complete coherent source-31 native tuple.
`coefficients/payloads/` contains four canonical unsigned little-endian
magnitudes in deterministic gzip files. `COEFFICIENT_BINDING.json` identifies
the tuple and shifted mask convention. The fixed leaves of the ten-integer
polynomial are the nine recipes in `data/coefficient_recipes.json` and
`beta_source = 2^2140030`. There is no unspecified universal-machine index,
existentially chosen coefficient, variable exponent, or extra quantified
intermediate register.

The complete native tuple is independently reproduced from the preserved
source builder and literal K215/943-tile data. Its four raw payloads total
533,099 bytes; their delivered compressed total is 10,485 bytes.

## Additional results

`short/` gives a local 74-operation equation of exact degree 68 in 15
positive variables:

```text
N0^2 + Na^2 + Ns^2 + (N1*Nk*Nt - 1)^2 - 3 = 0.
```

The three first norms are unconditionally nonzero, so their squares are at
least one. The minimum-sum equality forces the same unit conditions as the
checked 75-operation equation. This is a modest one-gate improvement, with
an ordinary local zero-equivalence proof; no new Lean theorem is claimed.
Its source-36 coefficient convention is kept separate from the main tuple.

`coefficient_adapter/` gives a separately proved native coefficient adapter
with base `2^429959` and 215,492 raw coefficient bytes, versus source44's
`2^590069` and 295,388 bytes. Its complemented labels and reused west parity
anchor resolve the earlier factorized receiver's empty-cell obligation.
The universal proof and the independent literal reconstruction are included.
These new coefficients are not substituted into the main equations.

## Read and reproduce

Start with `report.pdf`; `report.tex` and both included LaTeX sections are
the complete article source. The main proof includes all source and finalizer
registers, the exact weight and target tables, the two source directions,
and the proof of the final single-polynomial equation. `SUPPORT_PROOF.md`,
`nine/PROOF.md`, `short/RESULT.md`, and
`coefficient_adapter/SEPARATED_PROOF.md` provide companion proof details.

From this directory, with Python 3 and its standard library:

```sh
python3 verify.py
```

The release verifier checks source provenance, rebuilds the new circuits
inside a disposable copy, compares the resulting polynomial data, runs
the independent finite auditors normally and under `python3 -O`, and
reconstructs the inherited native coefficients. It does not modify the
release. If present, `MANIFEST.sha256` is also verified.

Individual commands are:

```sh
python3 code/build.py
python3 code/audit_candidate.py
python3 nine/build_nine.py
python3 nine/verify_nine.py
python3 short/verify_p74.py
python3 coefficients/reconstruct_native.py
python3 coefficient_adapter/build_separated.py
python3 coefficient_adapter/audit_separated.py
```

The builders update their own generated files. The source-31 builder is
preserved byte-for-byte and executed only in a temporary staging directory
by its reconstruction wrapper. The upstream historical builders are retained
for provenance and are not intended as entry points in this rearranged package.

For the document, use a TeX Live installation with the standard packages
listed in the preamble:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The explanatory figure and target table are already included. Recreating
the figure additionally requires matplotlib: `python3 code/make_figure.py`.
The finite mathematical audits do not require matplotlib, SymPy, or LaTeX.
The optional target search is a discovery aid; its running time and random
trajectory are not part of the proof or required for reproduction.

## Proof boundary and interpretation

The new source reductions are ordinary mathematical proofs; the finite
algebra and circuit certificates are executable exact checks. The unbounded
solvability theorem composes those results with the inherited positive-parent
compiler, K215/refutability calibration, and numerical Lucas/Jones bridges.
Their statements, source files, and provenance are identified in the article.

The archive does **not** contain a newly checked end-to-end Lean/Rocq proof
of the explicit native compiler or an exported object-language ZFC
derivation. Existing local kernel theorems and existence-selected polynomial
theorems are not represented as certificates for this explicit circuit.
The finite sample replays are labeled diagnostics and are distinguished
from the exact symbolic extraction and leading-coefficient certificates.

No global optimum is claimed. In particular the inherited 67-operation
equation remains shorter if arithmetic size alone is prioritized and 15
positive variables are acceptable. The principal improvement here is at
the low-variable explicit degree/circuit frontier. Interpreting the
nine-variable equation over unrestricted integers is not justified.

## Incorporation and attribution

This directory can be placed as a new report package under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/` and linked
from its collection README and incoming ledger. No existing directory or
package number is overwritten. Preserve `NOTICE.md`, `LICENSE`, the source
pins, and the inherited license files when incorporating it.

`SOURCES.json` and the per-component provenance records pin imported files
to the reviewed commit. `MANIFEST.sha256` hashes the released files except itself and the final
verification receipt written after the manifest check. The
native coefficients, quadratic parent, arithmetic bridges, and earlier
research directions retain their original attribution. The instantiated
selective certificate, shared positive-word encoding, optimized targets,
new source proofs and circuits, P74 observation, and parity-anchor adapter
are the contributions of this package.
