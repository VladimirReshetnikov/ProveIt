# Beyond Dirichlet GRH

**Validated arithmetic and transferable proof machinery**  
Prepared for Vladimir Reshetnikov, 25 November 2026 (Pacific time).

Read `report.pdf`; its complete editable source is `report.tex` plus `sections/*.tex`.

## Main conclusions

1. **A substantive prior arithmetic completion is revalidated.** The earlier ProveIt report `grh-exponent-six-and-transfers.zip` eliminates the residual discriminant interval that remained in the published exponent-six imaginary quadratic class-group classification even under ERH. Exactly **432 fields** occur, with largest absolute fundamental discriminant **5,761,140**. The corresponding order classification has **1,236 orders**, with largest absolute discriminant **43,522,752**. Both complete paired-norm searches were replayed: each tested **9,393,302** relevant candidates and found **zero survivors**. The published exhaustive census through 3.1×10^20 and the published conductor classification remain explicitly identified inputs. This report validates earlier work; it does not claim to have discovered that completion in this session.

2. **A concrete nonabelian local input is constructed.** For the totally real S3 splitting field of T^3−4T+1, the report gives an exact integral trace frame, extends it across the actual cyclotomic intersection, proves a Frobenius-partner congruence at inert primes, and realizes a complete-splitting selector. Two explicit primes in the same arithmetic progression are distinguished. The global odd-cocycle, integral-lattice, level-prime and spanning estimates needed for a new nonabelian zero theorem remain open.

3. **Two analytic interfaces are developed.** A joint-filter theorem repairs individual averaging kernels with hidden spectral zeros. A sharp positive-ramp moment theorem identifies the exact loss in recovering pointwise control and supplies a countermodel with bounded positive real coefficients on integer support. These have complete written proofs and independently reviewed constants; their elementary algebraic pieces are also checked in Lean.

The full upstream theorem is RH and GRH for **Dirichlet** L-functions. This report does not assert nonabelian GRH, Artin holomorphy, or a new Selmer/K-group vanishing theorem. It does not claim worldwide novelty for classical trace-form or interpolation ingredients.

## Contents

| Location | Contents |
|---|---|
| `report.pdf`, `report.tex`, `sections/` | Complete report, proofs, source map, research agenda and bibliography |
| `code/` | Exact checkers, figure generation, PDF builder and replay driver |
| `formalization/` | Seven compiled elementary Lean lemmas and pinned project configuration |
| `prior/exponent_six/` | Earlier checkers and tables, unchanged, plus fresh execution logs |
| `prior/cm_inputs/` | Selected prior CM data used only for limited input checks |
| `evidence/` | All-26 prior report inventory and claim matrix; independent review; selected upstream source snapshot and provenance |
| `validation/` | Exact arithmetic certificates, actual Lean compilation log and quality checks |
| `figures/` | Exportable PDF/PNG figure and its data |
| `licenses/` | Upstream notices and attribution |
| `SHA256SUMS` | Final package integrity hashes |

## Reproduce

Quick exact checks, from this directory:

```sh
python3 code/reproduce.py
```

Both full census searches and the exact rational explicit-formula certificate:

```sh
python3 code/reproduce.py --full-census
```

Build the PDF:

```sh
python3 code/build_pdf.py
```

Dependencies: Python 3; SymPy for the field/frame checker; a C++17 compiler for the second full search; Matplotlib only for regenerating the figure; a LaTeX installation for the report. The mathematics does not depend on the floating-point illustration. The replay driver creates a fresh workspace under `validation/replay/` and preserves the supplied certificates.

For Lean, see `formalization/README.md`. The successful compilation recorded here used Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The seven lemmas are elementary components, not an end-to-end formalization of the report.

## Source pins and validation limits

- Upstream: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207
- Prior reports: https://github.com/VladimirReshetnikov/ProveIt/tree/6fe2c1bd450aa7f19eab17fb9a6e76170b4fce00/docs/incoming
- Complete external verification of the upstream development is reported by Andrew Sutherland and Michael Rubinstein; this session inspected the source and compiled the separate small Lean file, but did not rebuild the complete upstream project.
- The initial low-discriminant census and the full set of older sparse-CM sieves were not rerun. The report distinguishes those published/prior inputs from computations performed here.
- Archive and source hashes are recorded in `evidence/`. Selected upstream files are preserved byte for byte with their original notices. Their licenses remain in force.

The report was compiled, visually inspected, and checked for unresolved references before delivery. Re-running it creates fresh logs rather than altering the delivered evidence.
