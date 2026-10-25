# Direct quartics from a nearest-factorial certificate

All final coordinates range independently over **unrestricted integers**.
The single equation is the sum of the squares of the complete quadratic
residuals in the selected `equation.json`. Its entire collected expansion is
also supplied. These are finite integer polynomials, with no variable powers
or unspecified coefficients in the actual equation.

| Endpoint | Variables | Quadratic rows | Degree | Collected terms | Height |
|---|---:|---:|---:|---:|---:|
| `equations/P242` | 242 | 178 | 4 | 17,026 | 38,432 |
| `equations/P243` | 243 | 179 | 4 | 6,877 | 11,856 |

P242 minimizes dimension within this release; P243 has substantially smaller
support and coefficient height. Neither is claimed globally simplest.
The matched incoming direct parent has 252 integer variables, 182 quadratic
rows, degree four, 5,340 collected terms, and height 128,446. Thus these are
variable/height improvements with an explicitly reported support tradeoff.

The mathematical change is the replacement of both one-sided factorial
ceiling guards by a normalized signed nearest-integer certificate. The new
nearest-factorial lemma, sign recovery, exclusion of zero and negative
branches, and constructive completeness are proved in
`proofs/NEAREST_FACTORIAL_PROOF.md`. An odd-square radix replaces the third
front guard; this parity construction is credited to the incoming symmetric
residue-budget work. Four affine consequences, credited to the incoming
residual-basis work, are transferred and checked exactly. The source uses
the numerical C222 proof calculus rather than K215 or Jones universality.

The ordinary mathematical theorem, composed with the named retained
C222/ZF/ZFC refutation calibration, is:

    ZFC proves: no integer zero exists if and only if Con(ZFC).

This release does not prove Con(ZFC) or supply a newly compiled end-to-end
Lean/Rocq or encoded object-ZFC proof. The retained formal interface files
are source evidence, not a claim that their transitive dependency closures
were rebuilt here.

## Exact data format

A term `[c,[i,j,...]]` means `c*x_i*x_j*...`, with repeated indices for powers
and `[]` for the constant. The final variable names are the literal symbols
`x0`, `x1`, and so on. Circuit names occur only in `source_name` provenance.
`coordinate_was_sheared` explicitly flags coordinates changed by a listed
integer shear; those source names must not be read as unchanged semantics.
All embedded final metrics agree with the coefficient files.

## Offline checks

Python 3.10 or later, standard library only:

    python3 -B verify.py --rebuild
    python3 -B -O verify.py --rebuild

The default checks ten deliberate corruptions in separate temporary copies.
`--skip-mutations` omits those controls. `--receipt PATH` saves a JSON receipt
outside the sealed component. The default is read-only. Rebuilding regenerates
the 246-coordinate intermediate and both final polynomials in temporary
folders and compares their bytes. The final replay executes only the frozen
finite transformation certificates; it does not rerun the row optimizer.

The independent checkers import no producing modules. They reconstruct all
source edits and guard identities, replay 18 Horn-factorization edits, 203
base monic projections, the coordinate translation, six coordinate shears,
five row-exposure operations, three or four further monic restorations,
all final row operations, and every collected quartic coefficient.
Finite checks supplement the ordinary unbounded proof; they do not replace it.

## Layout

- `data/`: complete 246-coordinate source-change and projection chain.
- `equations/P242/`, `equations/P243/`: final polynomials and finite certificates.
- `code/`: producer, frozen replay, and separately implemented checks.
- `proofs/`: new proof and identified immediate predecessor arguments.
- `upstream/`: retained arithmetic/calibration proof closure and source notices.
- `PROVENANCE.json`: pinned input identities and archive hashes.

New material was prepared with AI assistance for Vladimir Reshetnikov and
ProveIt on 25 October 2026. Copied material retains its original notices.
