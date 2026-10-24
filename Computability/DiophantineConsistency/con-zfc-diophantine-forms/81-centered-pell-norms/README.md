# Centered Pell norms and shared positivity

This contribution supplies seven explicit fixed Diophantine equations and
ordinary mathematical proofs of their equivalence to finite ZFC refutability,
using the pinned ProveIt native/compiler calibration. It adds five useful
unrestricted-integer variable/degree tradeoffs and two positive-integer
improvements. The leading result has **22 integer unknowns, degree 14, ten
squared residuals, and 123 live binary arithmetic operations**.

The source comparison is the complete catalogue, including sources 31–75,
at ProveIt commit `2605669a532342f153b13eb6b4a0af4b54f5fa37`. No new source
number is reserved by this archive.

## Results

| Literal polynomial | Domain | Unknowns | Exact degree | Binary operations |
|---|---|---:|---:|---:|
| `integer/sextic31.json` | all integers | 31 | 6 | 144 |
| `integer/octic26.json` | all integers | 26 | 8 | 131 |
| `integer/degree10_24.json` | all integers | 24 | 10 | 135 |
| `integer/degree12_23.json` | all integers | 23 | 12 | 122 |
| `integer/degree14_22.json` | all integers | 22 | 14 | 123 |
| `positive11/p11_positive_degree277.json` | strictly positive integers | 11 | 277 | 111 |
| `positive12/equation.json` | strictly positive integers | 12 | 78 | 103 |

For every row, the mathematical conclusion, with the inherited syntactic
consistency predicate, is

> ZFC proves: the displayed polynomial has no zero in its declared domain
> if and only if Con(ZFC).

The new algebraic reductions are proved in the report. Their final
refutation interpretation imports the identified ordinary native/compiler
and canonical-witness theorems. This is **not a new end-to-end Lean/Rocq
certificate or an actual object-language ZFC derivation file**. The exact
formalization boundary is documented below and in the retained upstream
status files. The equation is not asserted to be globally simplest.

All integer equations are sums of squares of their listed residuals. The
positive equations use proved unit-product finalizers; do not change their
domains to unrestricted integers or nonnegative integers without another
reduction. The 25-integer degree-12 packet is retained solely as a dominated
intermediate in the elimination chain and is not counted as an endpoint.

Operation counts charge each live binary `+`, `-`, and `*`, including
squaring and scalar multiplication; fixed numerals and reuse are free.
They describe the supplied circuits, not optimal circuits or bit complexity.
Some input coefficients exceed a million bits. Counts, degrees, variable
numbers and coefficient sizes are separate measures of simplicity.

## Read the argument

- `report/report.pdf`: complete typeset article.
- `report/report.tex` and its four included `.tex` sections: editable sources.
- `integer/PROOF.md`: complete 23-integer system, the 24- and 22-integer
  extensions, and their two-way witness transformations.
- `validation/POSITIVE_COMPOSITION_REVIEW.md`: separately conducted
  mathematical review of the positive constructions.
- `integer/INTEGER23_MATHEMATICAL_REVIEW.md` and
  `integer/INTEGER_EXTENSIONS_MATHEMATICAL_REVIEW.md`: independent internal
  mathematical reviews of the integer constructions.
- `exploratory/HOMOGENEOUS_CLOSURE.md`: separate CRT index-elimination theorem.
  This is a compiler-stage result, **not an eighth completed ordinary
  consistency equation**.

### Main mathematical contributions

The 23-integer equation composes source 75's signed-power bootstrap,
source 71's calibrated determinant, and source 68's shared positivity
certificate. The resulting degree budget permits elimination of three
additional coordinates. Its full degree-12 leading form is

```
256 beta^4 J^4 u^8 + I^4 f^4 o^4 + eta^4(-fo+jc+hE)^4.
```

Two further mechanisms yield the other principal endpoints:

1. **Center the auxiliary root:** `y_old=fo+y`, `V=fo-c`, so
   `y_old^2-V^2=(c+y)(2fo+y-c)`. The leading square cancels.
2. **Reduce the main norm on a nonzero scale:** with `Y=a-E`, `b=ac+gamma H`,
   `N=(X+b)^2-Delta c^2-1`, use
   `M=YN+(X+2b)(E-XY)` in the presence of `E-XY=0`. The other scale row
   forces `Y=(2v+1)q^3!=0`, since `q=beta J+1` and `beta>1`. This
   replacement is reversible and gives 24 variables at degree 10.
3. **Remove the strong ordinate before eliminating it:** for
   `S=I^2-Delta(f^2-1)`, replace the old auxiliary residual by
   `A_old+S(y_old^2-V^2)`. Then eliminate `I=(2r+1)c^2`. Together with
   centering, this gives 22 variables at degree 14.

The complete leading parts for the last two constructions are

```
P24: 64 a^4 gamma^2(c+2gamma)^2(a-E)^2 + 4 I^4 f^2 o^2(c+y)^2,
P22: 4 a^4 f^6 o^2(c+y)^2.
```

Each has a displayed coefficient equal to 4, proving the exact degree
independently of relations among the fixed coefficient ports.

For the 11-positive-variable equation, adjacent-coefficient Pell descent
allows `I=i*c^2` instead of `I=i*q*(q-1)*c^2`, lowering degree 325 to 277
and operations 113 to 111. For 12 positive variables, the adaptive carrier
`S=4qY`, `U=4q^2Y` lowers degree 82 to 78 at a cost of one operation.

The constituent positivity and descent lemmas already occur in upstream
packages; the report distinguishes inherited ingredients from these new
compositions and the new centered-norm transformations. Historical priority
outside the inspected repository is not claimed.

## Reproduce

Use Python 3.10 or later, with the standard library only. From the extracted
archive directory run:

```sh
python3 verify.py
```

This authenticates all pinned local sources and coefficient payloads,
rebuilds the positive tuple from the literal transition table, regenerates
the exact polynomial packets and circuits, compares the regenerated bytes,
and runs the exact algebra audits and separate finite diagnostics. The full
integer equations are expanded symbolically by the independent checkers.
The larger positive equations are checked through exact polynomial cuts
and nonzero specialized leading-coefficient certificates. The checks have
also been run with Python optimization enabled:

```sh
python3 -O verify.py
```

The program writes a short aggregate receipt to
`validation/VERIFICATION.json` and component receipts beside each checker.
It neither searches for a ZFC refutation nor tests consistency. Universal
existence equivalences come from the written proofs, not finite sampling.

Rebuild the report separately with a standard TeX installation:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

`MANIFEST.sha256.json` records the release file hashes. The top-level verifier
checks those hashes before rebuilding. Deliberate edits should be reviewed
and the manifest regenerated; it is an integrity record, not a signature or
a proof certificate. Runtime receipts and TeX build scratch files are not
included in that manifest.

## Fixed coefficients: two coherent tuples

The integer forms use the entire source-34 tuple and source-71 scales:

```
beta = 2^1064921 - 1,
cone_A = 2^1113,
cone_B = 2^666104,
K0, MC, MF = the authentic source-34 native ports.
```

All six exact unsigned integers are stored in
`integer/coefficients/*.bin.gz` as gzip-compressed minimal unsigned
little-endian bytes. `integer/coefficients/BINDING.json` specifies their
SHA-256 hashes, lengths and source binding. These six payloads contain
615,883 raw bytes. No coefficient is an unspecified existential parameter.

The positive forms use the separate compact source-44 tuple with
`beta=2^590069-1`; its four complete payloads total 295,388 raw bytes.
`coefficients/ACTIVE_BINDING.json` binds the ports `beta,K0,MC,MF` to those
files, and `coefficients/recipe/` contains the literal recipe, restored
pinned dependencies and its inherited proof. In both tuples, `MF` is already
shifted. Never mix ports between tuples or apply that shift a second time.

For example, an exact integer can be loaded without decimal conversion:

```python
import gzip
from pathlib import Path
beta = int.from_bytes(
    gzip.decompress(Path("integer/coefficients/beta.bin.gz").read_bytes()),
    "little",
)
```

## Calibration and formalization boundary

The integer results inherit the signed/native/compiler calibration and
canonical-witness results identified in sources 64, 71 and 75. The positive
results inherit the source-44 tuple, source-61 normalized Pell interface,
and source-69/source-70 carrier theorems. The relevant proof files are
included, with hashes and upstream paths; the full original repository is
identified by its commit.

`provenance/NATIVE_CALIBRATION52.md` records the difference between native
arithmetic theorems and a complete formal calibration of a particular native
tuple to K215. `provenance/OBJECT_ZFC.md` records the separate distinction
between an external equivalence and an actual derivation in the encoded ZFC
calculus, including nonstandard internal naturals. This contribution
supplies neither missing end-to-end formal derivation. It provides ordinary
proofs of the new reductions and explicitly imports the stated ordinary
calibration, rather than treating hashes, bounded tests, or an external
Lean equivalence as a substitute for that calibration.

The CRT appendix proves a different index-elimination lemma by homogenizing
the proof-checker polynomial. Factorial, binomial and bounded-closure
relations remain uncompiled there. It is a concrete alternative-route result
with an explicit remaining task, not a new non-K215 consistency endpoint.

## Licensing and provenance

The new contribution is offered under the repository's MIT No Attribution
license in `LICENSE`. Retained upstream notices are in `licenses/`,
`integer/licenses/`, and `coefficients/recipe/licenses/`. See `NOTICE.md` for
attribution and modification details. Source numbering, filenames and old
commit strings inside unmodified proof files are intentionally retained.

`CATALOGUE_ENTRY.md` gives a proposed integration entry, without modifying
the repository or reserving a package number.
