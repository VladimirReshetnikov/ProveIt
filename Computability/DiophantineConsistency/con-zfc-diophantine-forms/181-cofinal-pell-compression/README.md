# Cofinal Pell centers and oriented power certificates

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

Start with **report/report.pdf**. The LaTeX source and every required generated
include are supplied. All four final equations have fixed integer coefficients
and **unrestricted integer variables**. The ordinary proofs, composed with the
identified inherited C222/ZF/ZFC refutation calibration, establish in ZFC that
a zero exists if and only if a finite syntactic ZFC refutation exists.
Negating this equivalence gives the requested consistency statement.

## Results

| Polynomial | Integer variables | Exact degree | Squared residuals | Collected monomials | Collected coefficient height |
|---|---:|---:|---:|---:|---:|
| Balanced one-square center | 229 | 4 | 176 | 4,477 | 7,968 |
| Compact one-square center | 228 | 4 | 175 | 12,001 | 7,968 |
| Split oriented pooling | 207 | 16 | 146 | 94,294 | 13,607,065,661 |
| Five-base oriented pooling | 206 | 24 | 145 | Not fully expanded | Not claimed |

The complete 206-variable polynomial is specified by its literal sum of squares:
144 quadratic residuals and one degree-12 residual. The latter has 25,144 terms.
Its compact factored specification is also complete. The 207-variable equation
has the same 144 quadratic residuals and degree-8 and degree-5 residuals.
Maximum *residual* coefficient in both pooled forms is 95,232; this must not be
confused with the coefficient height of the collected final polynomial.

The quartics improve their matched package-166 parents by one variable and five
monomials each, at unchanged degree and height. Pooling removes nine or eight
private certificate variables from the source of package 173's 215-variable
quartic, at increased degree. Existing smaller-variable high-degree and
large-coefficient equations remain different tradeoffs. There is no global
minimum or worldwide-priority claim.

## New arithmetic

1. **One scaled square for a free Pell center.** For an even frame, a cofinal
   choice of its Pell index permits `A = L^2 + 2u^2`, replacing two separate
   squares. An order-eight identity in a finite quadratic algebra supplies
   the local square class. The existing completeness parities let the source
   frame change only from `W = 2 + sum(atom^2)` to `W = 3 + sum(atom^2)`.
   This deletes a private integer coordinate without a new row.
2. **Oriented reciprocal pooling with initially zero bases.** Weights `n_j`
   make all nonzero terms of the rational squared-error sum have the same
   sign. The theorem recognizes every nonzero-base block; zero-base blocks
   contribute zero until unchanged parity equations exclude them. Five bases
   share one integrality witness, or three share one and the final two another.

The first change uses a new cofinal completeness argument; it is not an inverse
map on arbitrary old center witnesses. The second is pointwise existential
equivalence over every retained parent coordinate and has explicit witness maps
in both directions. The report treats these distinctions separately.

## Exact files

- `equations/P229_balanced/` and `equations/P228_compact/`: every quadratic
  residual, collected coefficient, metric, coordinate name, and construction
  certificate; readable text and LaTeX versions accompany the JSON.
- `pooling/oriented_pool/principal206.json`: complete literal 206-variable
  residual polynomial; `principal206_factored.json` specifies the much shorter
  equivalent finite formula.
- `pooling/oriented_split/principal207.json`: complete 207-variable residual
  polynomial; its factored version and full collected expansion accompany it.
- `proofs/`: both unbounded new arithmetic arguments and their source boundary.
- `reviews/`: independently assigned AI mathematical reviews; these are not
  external human refereeing.
- `verification/`: actual finite-check receipts.
- `inherited/` and `pooling/173-crt-index-anchor-215/`: selected unchanged source
  data, certificates, proofs, and notices. These are a scoped dependency subset,
  not a full standalone copy of either historical package or a complete Lean
  dependency closure. Historical README claims describe their original releases.

Each term `[c,[i,j,...]]` means `c*x_i*x_j*...`, and `[c,[]]` is a constant.
Every index is zero-based. All residual lists are finite and every declared
final coordinate occurs. Named gates and factored expressions add no unknowns.

## Reproduce the checks

Python 3.10 or later and its standard library suffice. No network is required.

```sh
python3 -B verify.py
python3 -B -O verify.py
```

The verifier checks the manifest when present, replays independent exact
coefficient audits, tests the new arithmetic fixtures, verifies the complete
factored definitions, and reconstructs the equations byte-for-byte in temporary
directories. It does not modify the delivered files. Save a separate receipt with
`--receipt /tmp/conzfc-replay.json`. Use `--skip-manifest` only after intentionally
editing a working copy; all mathematical checks still run.

Focused checks:

```sh
python3 -B code/check_endpoint_delta.py
python3 -B code/check_frame_parity.py inherited/package166/stages/compressed/raw_source.json
python3 -B code/check_one_square_center.py
python3 -B pooling/check_oriented_independent.py --root pooling
```

Rebuild the equation definitions in new directories:

```sh
python3 -B code/build_one_square.py --output /tmp/conzfc-quartics
python3 -B pooling/build_oriented_pool.py --output /tmp/conzfc-206
python3 -B pooling/build_oriented_pool.py --split --output /tmp/conzfc-207
```

The independent pooling audit reconstructs the full 207-variable expansion.
No program attempts the enormous full expansion of the 206-variable SOS.

## Evaluate a supplied tuple

```sh
python3 -B evaluate.py 229 point.json
python3 -B evaluate.py 206 point.json --residuals
```

Replace the profile by `228` or `207` as desired. The input is a JSON list of
exactly that many integers. This evaluates a specified tuple; it is not a root
search or a consistency decision procedure.

## Rebuild the article

Use a working copy when changing generated artifacts. With standard TeX Live:

```sh
python3 -B code/export_pooling.py
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The final run settles table-of-contents pagination. The PDF was rendered and
visually checked. PDF metadata/fonts can differ across installations; exact
polynomial identities are the coefficient data and residual definitions.

## Provenance and proof boundary

The repository comparison pin is
`02a78a08603cbae248c19c23a75907c6c6bd6443`.

The center branch builds on package **166-fixed-base-modular**. Its finite
quadratic-ring/odd-order setup is inherited; the even-frame order-eight argument
and one scaled square are the new refinement. The pooling branch builds on
**173-crt-index-anchor-215** and the two-base lemma of
**168-reciprocal-pooling**. The multi-base direction had been suggested there;
the signed orientation, inactive-zero treatment, parity activation, and literal
206/207-variable equations are the present completion.

The logical interfaces are `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Source excerpts are
retained. The unbounded C222 calibration and the older signed Pell/CRT compiler
remain credited dependencies. No freshly compiled end-to-end Lean/Rocq theorem,
object-language ZFC derivation, or consistency decision is claimed. Finite checks
authenticate artifacts and supplement the proofs; they do not prove quantified
semantic statements by testing examples.

`RESULTS.json` gives all four profiles in one machine-readable table.
See `INTEGRATION.md`, `PROVENANCE.json`, `NOTICE.md`, and `MANIFEST.sha256`.
