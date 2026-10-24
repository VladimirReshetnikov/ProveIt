# Reusing witnesses in Diophantine consistency equations

Prepared for Vladimir Reshetnikov's ProveIt research program, 24 October 2026.

The principal result is a completely specified ordinary integer quartic

\[
P_{508}(x_0,\ldots,x_{507})=\sum_{j=0}^{307}Q_j(x_0,\ldots,x_{507})^2.
\]

All 308 quadratic residuals are printed in `report/main.pdf`, Appendix A,
and supplied literally in `direct/principal/equation.json`. All 6,545
collected coefficients are supplied in `direct/principal/expanded_polynomial.json`.
The equation has 508 occurring unrestricted integer variables, exact degree
four, and coefficient height 996,521.

Composed with the inherited, identified C222/ZF/ZFC calibration, the ordinary
proof establishes

\[
\mathrm{ZFC}\vdash
\left[\forall\mathbf x\in\mathbb Z^{508}\;P_{508}(\mathbf x)\ne0\right]
\longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

This does not assert consistency, a global minimum, literature-wide novelty,
or a new complete proof-assistant formalization. The direct construction
encodes a numerical proof calculus; it does not simulate K215 or instantiate
Jones's universal polynomial. The separate positive companions inherit the
native K215 calibration and explicitly state their different domain.

## Concrete results

| Direct construction | Integer variables | Quadratic rows | Degree | Collected terms | Height |
|---|---:|---:|---:|---:|---:|
| Matched incoming Round 14 parent | 517 | 310 | 4 | 6,774 | 3,904,267 |
| Cofinal checkpoint | 512 | 310 | 4 | 6,742 | 3,904,268 |
| **Principal signed-factorial construction** | **508** | **308** | **4** | **6,545** | **996,521** |
| Separate existing lower-height alternative | 519 | 321 | 4 | 6,253 | 411,060 |

The new principal equation improves every varying metric of the matched
517-variable parent. The 519-variable alternative remains useful when height
or term count is the priority. Other repository branches already have far
fewer variables with very large fixed coefficients, including a 37-integer
quartic. This packet does not claim to improve their variable counts.

The six companion equations in `positive/equations/` use exactly ten
**strictly positive** unknowns. Their operation-count/degree pairs are
89/288, 91/283, 92/278, 94/262, 96/258, and 97/254. Full fixed coefficient
payloads and a deterministic finite reconstruction recipe are included.
Operation counts count live binary additions, subtractions and multiplications;
they are not bit-complexity measurements.

## The new mathematical steps

1. Choose the proof horizon from the cofinal family `t = 16 + s^2`.
   Completeness permits every sufficiently large padded horizon, so all
   dependent witnesses can be regenerated after this choice.
2. Reuse the existing power `V = (F^2 t^2 + 1)^t` as a bound on every
   pending-product accumulator, and set `y = V(V-1)`.
   At the canonical value `F = t!`, this is a sufficiently large positive
   multiple of `F`, so the CRT modulus no longer needs a free slack guard.
3. Recover the sign of `F` from the raw equations. The product of consecutive
   integers `V(V-1)` is nonnegative for every signed integer V, so every
   required seed index is positive before indexed Pell semantics is invoked.
   Subsequent orientation makes `V` positive; the raw ceiling identity then
   makes `F` positive. A proved factorial lemma at radius `F^2 t^2` recovers
   `F = t!`. No exceptional zero-output case is needed.
4. In the positive branch, the existing fused Pell coordinate yields the
   fifth-index gap `b > 8Q`. This supports a shorter transport multiplier
   and, at the lowest evaluation cost, removal of the product center.

These are existence-preserving transformations. Completeness reconstructs
witnesses from a finite refutation; it does not restrict every arbitrary old
zero pointwise. The distinction is essential.

## Contents

| Path | Purpose |
|---|---|
| `report/main.pdf` | Complete article, including all 308 principal residuals |
| `report/main.tex` and companion `.tex` files | Editable article sources |
| `direct/principal/` | Principal 508-variable equation, full expansion, exact maps, proofs, builder and independent checker |
| `direct/` | Complete 512-variable checkpoint and its literal 517-variable parent |
| `positive/` | Six ten-positive-variable circuits, actual coefficient payloads, recipe, proofs and independent checks |
| `proofs/` | Full cofinal and consecutive-modulus signed-factorial arguments |
| `inherited/` | Selected unchanged mathematical dependencies and calibration interfaces |
| `review/` | Independent mathematical review records and release verification receipts |
| `SOURCE_LEDGER.json` | Source paths and hashes for retained logical dependencies |
| `RELEASE.json` | Machine-readable principal claims and exact equation hashes |
| `MANIFEST.sha256` | Hashes of all released files other than the manifest itself |

The JSON sparse convention represents a term as `[coefficient, [indices]]`;
indices are zero-based and repetitions are powers. For example,
`[-3, [7, 7]]` means `-3*x_7^2`, and `[2, []]` means the constant `2`.
The JSON and main article use zero-based coordinates. The separately retained
`direct/principal/residuals508.tex` uses one-based display indices and is not
the source of the main article's appendix.

## Verify and reproduce offline

Python 3.10 or later and its standard library suffice. From this directory:

```sh
python3 -B verify_all.py
python3 -B -O verify_all.py
python3 -B verify_all.py --regenerate
```

The last command also rebuilds the principal and checkpoint artifacts in a
temporary directory and compares every emitted JSON file byte for byte.
All checker failures use explicit exceptions and remain active under `-O`.
No network connection, repository checkout, CAS, or external proof assistant
is required for these finite checks.

The checker validates the release manifest, inherited source hashes, all
finite source transformations, the full collected quartic, all six circuits,
the actual native coefficients, and the generated residual appendix. It also
runs clearly labeled finite semantic regression tests. These tests do not
prove the quantified arithmetic lemmas or establish that the equations have
no solutions. Read the mathematical proofs for those implications.

To rebuild the PDF with a standard TeX Live installation:

```sh
cd report
python3 -B generate_residuals.py --check
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The packaged PDF was rendered and visually inspected. PDF reproduction need
not be byte-identical because TeX embeds build metadata. Check the original
manifest before rebuilding. The `--skip-manifest` switch supports working
copies after intentional edits; it does not relax the mathematical artifact
checks. Use `--output /tmp/conzfc-receipt.json` to retain a fresh aggregate
receipt without altering the released files.

## Provenance and integration

Source repository: <https://github.com/VladimirReshetnikov/ProveIt>, frozen
at commit `45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`. The incoming Round 14,
saturated-Pell, and structural-compression packets are specifically credited
in the article and source ledgers. The current active files and all eight
incoming archives at that snapshot informed the comparison.

The supplied Lean files document named inherited interfaces; their full
transitive import closure has not been rebuilt. The new result is an ordinary
mathematical proof formalizable in ZFC, with exact finite artifact checks.
Retain that distinction when incorporating this contribution into ProveIt.

AI assistance was used in this research and preparation. Inherited notices
are retained. New material is offered under the repository's MIT No
Attribution terms; see `LICENSE.UPSTREAM` and `NOTICE.md`.
