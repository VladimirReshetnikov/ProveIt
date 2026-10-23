# Smaller explicit Diophantine forms of ZFC consistency

This contribution combines the constructions in ProveIt's current catalogue
with new quotient shifts, root bounds, signed-coordinate arguments, and the
existing odd-scale theorem. The full mathematical article is `report.pdf`;
its sources are `report.tex` and `integer17_section.tex`.

**For each delivered form, the stated theorem is that ZFC proves its lack of
solutions equivalent to Con(ZFC).** This is a theorem about an equivalence,
not a proof of either Con(ZFC) or its negation. The exact domain of the unknowns
is essential.

The inspected source revision is
`ae3007ca4467011e0e051c84acb4a1dd13971b0e` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/ae3007ca4467011e0e051c84acb4a1dd13971b0e/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms).
No repository branch, commit, or pull request was modified.

## Results

| Form | Quantified domain | Equations | Exact degree | Binary arithmetic operations |
|---|---|---:|---:|---:|
| Shifted norm product | 12 positive integers | 1 | **1097** | **116** |
| Shifted norm comparison system | 12 positive integers | 3 | **1088 maximum** | **110** |
| Shifted norm sum of squares | 12 positive integers | 1 | 2176 | 118 |
| Signed Jones construction | **17 unrestricted integers** | 1 | `424296*5^33+53824` | 20,607 |
| Odd-scale quartic | **51 unrestricted integers** | 1 | **4** | Not optimized |
| Odd-scale sextic | **42 unrestricted integers** | 1 | **6** | Not optimized |
| Odd-scale octic | **36 unrestricted integers** | 1 | **8** | Not optimized |

The degree of the seventeen-variable form is exactly
`49,394,555,389,881,134,033,203,178,824`.

All counts include every quantified unknown. Circuit registers are abbreviations
for polynomial expressions, not additional quantified variables. Binary `+`,
`-`, and `*` each cost one operation, including multiplication by numerical
constants; sharing a previously computed value and comparing two sides are free.
System degree is the maximum degree of its residual polynomials.

### What improves

* The previous best twelve-positive-variable degree in the inspected collection
  was 1145 at 123 operations. The new product has degree 1097 at 116 operations.
  Compared with the old 116-operation product of degree 1353, it saves 256 in
  degree. The new comparison system saves two operations against the old
  112-operation systems and has maximum degree 1088.
* The seventeen-integer form improves the explicit 26-integer count in the
  inspected direct compiler family, at the cost of a much greater degree and
  a much longer circuit.
* The quartic, sextic, and octic integer counts decrease from 54, 45, and 39 to
  51, 42, and 36. Their equivalent residual systems contain, respectively,
  30 quadratics, 21 polynomials of degree at most three, and 15 polynomials
  of degree at most four.

These are improvements under specified criteria, not a claim of a globally
simplest Diophantine equation. The catalogue's nine-natural-variable form,
67-operation single equation, and 59-operation system remain better on their
respective axes. Sun's 2026 general representation theorem gives a ten-integer
bound for recursively enumerable sets; a concrete ten-variable specialization
is not constructed here. See the article for primary references and precise
comparisons.

## Main ideas

### Twelve positive variables

Start with the existing norm construction, replace its positive index quotient
by `h_old = q + h`, and use the separation weight `W = I*(T+I)`. The new
pre-root inequalities prove `a*c > R*Delta` directly from the outer integer
unit equations. The exact square comparisons then bound every conjugate of
the auxiliary root by `W*sqrt(G)`. This allows the much smaller weight without
assuming the Pell classification before the roots have been recovered.

The polynomial is `P12 = Nk*Nt*(1+N)-1`, where `N` is the explicit eight-factor
conjugate norm in the article. All radicals cancel identically. A parity
identity excludes `N=-2`, so a zero enforces the intended norm and unit
conditions. A separate Pell argument proves that the quotient shift loses
no canonical witnesses. The emitted JSON gives the complete radical-free
arithmetic DAG.

The 110-operation system also substitutes `z_old=z+1` in the transport equation
and compares `N0*N0` directly with `G*N1*N1`. The product and this system have
equivalent solvability predicates, but the coordinate named `z` is shifted;
their named-coordinate zero sets are not identical.

### Seventeen unrestricted integers

The eight-coordinate Jones ratio interface has two guards that can be recovered
semantically. Six remaining nonnegativity guards and a strict margin are packed
into one square condition using seven pairwise coprime Pell factors. The
intersective polynomial `(t^3-t-1)*(t^2+23)` merges divisibility and the required
nonzero conditions. A separated three-root norm supplies the final equation.

The seventeen supplied coordinates are the eight original signed coordinates,
seven Pell witnesses, and two finalizer coordinates. The article proves the
nonzero, sign, valuation, complex-root, and guard-recovery cases explicitly.
Every source constant and every universal-polynomial index is fixed by an exact
finite recipe; none is an unspecified machine parameter.

### Low-degree integer forms

The existing odd-scale theorem makes one positivity representation redundant.
Replace the retained scale `s` by `2*v_scale+1` and delete its three positivity
parameters and one residual. The inherited arithmetic equations force this
odd scale to be positive, and canonical accepting witnesses already have odd
scale. The affine substitution preserves the degree bounds. Exact nonzero
coefficients prove degrees four, six, and eight rather than just upper bounds.

## Coefficients and provenance

`INSTANCE_BINDINGS.json` records the authoritative binding of each family.

* **Norm12 and low-degree forms:** the entire compact 943-tile tuple, with
  `B=2^(5^10)`, as specified in the root `COEFFICIENT_BINDING.json`.
  All four exact coefficients are supplied in deterministic gzip format under
  `coefficients/coefficients_compact/`; together they occupy 20,260 compressed
  bytes and decompress to 5,312,269 bytes. The port `MF` means
  `MF_source=MF_native+B-1`, never `MF_native`.
* **Signed17:** the entire original package-18 T4 tuple, with `B=2^(5^18)`.
  Its binding, exact quartic, finite index recipe, and generators are included
  under `signed17/upstream/`. Its very large derived constants are represented
  by exact finite formulas rather than materialized decimal strings.
  `signed17/SOURCE_PINS.json` authenticates all 19 imported source files by
  both Git blob identifier and SHA-256.

Do not substitute individual coefficient ports from a different backend.
Unchanged parent files retain their original bindings for provenance; those
bindings do not override `INSTANCE_BINDINGS.json` for the new outputs.
`coefficients/UPSTREAM_BINDING.json` preserves the original source manifest,
including its historical paths and earlier internal revision identifier.

## Reproduce the finite checks

Use Python 3.10 or later, without optimization (`-O`). No third-party Python
packages, network access, external repository, or proof assistant is needed.
From this directory:

```sh
python3 -B reproduce.py
```

The driver regenerates every main family, verifies the reported counts and
degrees, authenticates the imported signed17 sources, and checks the four
compact coefficient payloads. It writes a receipt and individual logs under
`verification/`. The generators also emit their detailed receipts alongside
their outputs.

`verification/SHA256SUMS` records the frozen release bytes. To check them before
regeneration, run `sha256sum -c verification/SHA256SUMS` from this directory.
Running the reproduction driver intentionally updates its timestamped receipt
and logs; regenerated mathematical circuit files remain deterministic.

To regenerate the compact coefficient integers themselves from the literal
machine and tile compiler, use:

```sh
python3 -B reproduce.py --materialize-coefficients
```

This additionally writes the four raw `.bin` files, approximately 5.3 MB in
total. The archive already supplies their exact gzip encodings.

Individual construction commands are:

```sh
python3 -B norm12/build_shifted_norm12.py
python3 -B signed17/build_signed17.py
python3 -B low_degree/build_odd_scale_lifts.py
```

To rebuild the article with a LaTeX distribution containing the listed packages:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

If `latexmk` is unavailable, run `pdflatex` repeatedly until cross-references
and the table of contents stabilize.

### Verification scope

The detailed receipts record exact independent norm evaluations, coordinate
shift identities, parity and circuit liveness, symbolic degree information,
coefficient-byte checks, actual fixed-instance modular comparisons, Pell gap
checks, and finite intersectivity diagnostics. Uniform mathematical arguments
establish the semantic reductions and exact degrees; finite tests support
those arguments and authenticate the emitted artifacts.

These checks do not search for a solution, prove its absence, or decide
Con(ZFC). They are not an end-to-end Lean or Rocq certificate. The ordinary
mathematical proofs import the identified Jones/compiler theorems and exact
K215-to-refutation calibration from the pinned repository. The article states
these dependencies and distinguishes them from the new reductions. No new
proof-assistant build was performed.

## Artifact map

| Path | Purpose |
|---|---|
| `report.pdf`, `report.tex`, `integer17_section.tex` | Full article and editable LaTeX |
| `norm12/shifted_norm12_product.json` | Degree-1097, 116-operation polynomial |
| `norm12/shifted_norm12_system110.json` | Three-equation, 110-operation system |
| `norm12/shifted_norm12_sos118.json` | Degree-2176 sum of squares |
| `norm12/*PROOF.md` | Detailed working proofs and intermediate bound derivation |
| `signed17/generated/signed17.json` | Complete 17-integer polynomial DAG |
| `signed17/SIGNED17_PROOF.md` | Complete signed-domain reduction proof |
| `low_degree/generated/integer*_odd_scale.json` | All residuals defining the three low-degree sums of squares |
| `low_degree/ODD_SCALE_LIFTS_PROOF.md` | Odd-scale composition and quotient recovery proof |
| `low_degree/INDEPENDENT_AUDIT.md` | Independent mathematical review of the new families |
| `coefficients/` | Literal coefficient data, finite generators, compiler proofs |
| `references/` | Pinned comparison and inherited proof interfaces |
| `verification/` | Reproduction receipt, logs, and artifact checksums |
| `NOTICE.md`, `LICENSE`, `licenses/` | Attribution and inherited licensing |

The intended integration is a new report directory in the cited ProveIt
collection. Keep the relative paths inside this archive intact. Consult
`NOTICE.md` for authorship and inherited-source attribution.
