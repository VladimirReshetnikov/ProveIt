# Smaller Diophantine formulations of Con(ZFC)

Research synthesis prepared for Vladimir Reshetnikov and the ProveIt repository,
22 October 2026. The inspected upstream snapshot is
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`.

Start with **report.pdf** or its editable source **report.tex**. The main theorem
is that, for each construction below, ZFC proves

    a solution exists <=> a finite ZFC refutation exists.

Consequently, ZFC proves that the absence of solutions is equivalent to
Con(ZFC). All principal constructions use **strictly positive integers**.
Nonnegative and unrestricted-integer conversions are specified separately.
This is a representation of consistency, not a proof of consistency.

## Results

| Construction | Positive variables | Equations | Degree | Binary operations |
|---|---:|---:|---:|---:|
| Ordinary input-free system S15 | 15 | 6 | 28 maximum | 61 = 34M + 27A |
| Product P69 | 15 | 1 | 99 exact | 69 = 39M + 30A |
| Sum of squares of S15 | 15 | 1 | 56 exact | 78 = 40M + 38A |
| Outer norm Psi14 | 14 | 1 | 342 exact | 73 = 44M + 29A |
| Product norm Phi14 | 14 | 1 | 293 exact | 75 = 44M + 31A |
| Ordinary quadratic lift | 33 | 24 | 2 maximum | Not optimized |
| Sum of squares of the quadratic lift | 33 | 1 | 4 exact | Not optimized |

Every binary addition, subtraction, or multiplication costs one, including
multiplication by a numeral. Constants, copying/reuse, and equality comparisons
are free under this convention. Circuit registers are polynomial abbreviations,
not additional unknowns. These are evaluator counts, not bit-complexity bounds.

The six-equation system combines package 06's removal of the input marker with
package 02's ordinary strong Pell norm. The proof establishes rank before
restoring the deleted auxiliary quotient. This reduces the prior degree-28
system from 16 variables, seven equations, and 63 operations.

The fourteen-variable equations combine the input-free parent with the signed
quadratic-root elimination of package 05 and the native complete90/92 notes.
The input-free signed-quotient theorem is supplied explicitly; merely squaring
away the root would not suffice. The 33-variable lift removes one register and
one equation from package 08's quadratic lift.

These are improvements within the inspected family. They do not establish
global minimality, a record variable/degree pair, or novelty against all
literature. The inherited 67-operation single polynomial still uses fewer
operations than the new single equations. Classical nine-unknown existence
theorems are a separate comparison, discussed in the report.

## The fixed coefficients

All four primary coefficients come **together** from the four-cell recipe in
`data/four_cell_constants.json` and `code/four_cell_compiler.py`.

| Report symbol | Circuit port | Definition |
|---|---|---|
| beta | `Bm1` | B - 1 |
| K | `Kconstant` | DC + B DR |
| MC | `MC` | Native lower mask |
| MFsrc | `MF` | MF_native + B - 1 |

Do not mix ports from different coefficient recipes. In particular, the shifted
source port `MF` is not the native upper mask.

The new local alphabet has exactly **71,356,645** tiles. The recipe has
B = 2^d with **d = 5^28**, instead of d = 5^67 in the inherited raw-K215
recipe. The exact reduction in the bit length of B - 1 is **5^39**.
The coefficients remain enormous. The archive contains unconditional finite
recipes, not expanded values or an accepting computation.

The immutable `vendor/fixed_blank_67.json` is the inherited arithmetic source.
The new scripts reuse its circuit skeleton and explicitly bind the emitted
packets to the new coefficient recipe. The complete original package-06
coefficient tuple is also valid for the new algebra, as a separate legacy choice.

## Files

- `report.tex`, `report.pdf`: the complete research report, formulas, proofs,
  comparisons, domains, source references, and verification limitations.
- `code/ordinary_start.py`: constructs and checks S15, P69, and the degree-56
  sum of squares.
- `code/root_elimination.py`: constructs and checks both fourteen-variable
  equations and their 38-integer-variable versions.
- `code/root14_independent_audit.py`: independent sparse-polynomial audit of
  the exact highest homogeneous forms, identities, and gate ledgers.
- `code/quartic33.py`: exact sparse quadratic residuals, projection identities,
  and the 72-variable quartic and 59-variable degree-eight integer variants.
- `code/four_cell_compiler.py`: exact machine binding, local tile census,
  coefficient recipes, layout checks, and finite semantic diagnostics.
- `data/`: the emitted circuits and certificates compared by the scripts.
- `SYMBOLS.json`: the main correspondences between report notation and
  circuit identifiers.
- `proofs/`: detailed ordinary proof notes and independent mathematical reviews.
- `vendor/`: the exact K215 table, transition export, and immutable parent circuit.
- `references/`: selected unchanged upstream proof notes for offline inspection.
  Their original paths and hashes are recorded in `PROVENANCE.json`.
- `licenses/`: inherited license and attribution notices.
- `verification_receipt.json`: the finite verification run supplied with this
  release.
- `MANIFEST.sha256`: SHA-256 digests of the release files other than the
  manifest itself.

The report calls the quadratic register `P_*`; the JSON/code name is `P`.
The code's `Baux` is the report's `B_a`. These are names for the same registers.
`SYMBOLS.json` maps the supplied unknowns, coefficients, and main abbreviations
to circuit identifiers. In particular the circuit register named `A` is the
report's discriminant Delta, not its Pell base A.

## Reproduce

Python 3.10 or later is sufficient; the verification scripts use only the
standard library. No network access or proof-assistant installation is required
for these finite checks.

~~~sh
python3 verify.py
~~~

Default verification compares committed data and does not regenerate it.
Each individual builder accepts `--write` to regenerate only its own packets.
To write a fresh aggregate receipt:

~~~sh
python3 verify.py --receipt fresh_verification.json
~~~

To check the integrity of the delivered release, without rerunning the algebra:

~~~sh
python3 verify.py --manifest-only
~~~

For the PDF, use a conventional LaTeX installation with pdfLaTeX and the standard
packages listed at the top of `report.tex`:

~~~sh
make pdf
~~~

The PDF build uses `.build/` for temporary TeX files. Rebuilding a PDF can change
its metadata and therefore its release hash. Intentional edits or regeneration
similarly require a new manifest before treating the directory as a new release.

## Verification boundary

The finite checks verify exact arithmetic identities, topology and operation
counts, exact highest homogeneous forms, quadratic projections, literal table
binding, the four-cell census, scalar geometry, and small diagnostic tableaux.
They **do not** prove the infinite Pell/compiler theorems by testing.

The mathematical proofs of the changes are ordinary proofs that can be
formalized in ZFC; they are not new Lean or Rocq developments. The report
identifies their inherited lemmas and the K215 ordinary calibration. The
upstream endpoint statement and its recorded verification were inspected,
but the complete Lean/Rocq builds were not rerun here.

This directory is self-contained for the finite verification and PDF rebuild.
It does not contain the entire upstream formal development or every recursively
referenced historical proof. The pinned repository remains the source for
that full dependency chain.

## Integration

The directory is intended as a new research package beside the existing
`con-zfc-diophantine-forms` packages. It does not replace or silently modify
an earlier construction. No repository changes or publication are included
in this deliverable. Preserve `PROVENANCE.json` and `licenses/` when integrating.
