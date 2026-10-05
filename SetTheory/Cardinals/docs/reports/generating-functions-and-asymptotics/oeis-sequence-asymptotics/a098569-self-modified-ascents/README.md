# Report242 Self modified ascent sequences and positive diagonal tables

This package contains a self-contained mathematical article and reproducible
checks for positive-diagonal upper-triangular integer tables and their binary
subclass. Size N is total entry sum, and dimension is the number of rows.
The exact enumeration and combinatorial bridges are prior work.

The current indexing is essential:

- b_0=c_0=1
- b_N=A098569(N-1) for N>=1
- c_N=A121690(N-1) for N>=1
- A098568(n,k)=T(n+1,k+1), so its column index is dimension minus one

## Results

The article proves an arbitrary fixed-order expansion at the exact gamma
saddle, uniformly for bounded real dimension marks. It includes global
localization, differentiated gamma estimates, a polynomial-Gaussian lattice
transfer, the full-span local Gaussian dimension law, and mean/variance
corrections. Thus it answers the row-distribution question in A098568 with
the correct size and column shifts.

For u(u+2)exp(u)=2N and P(u)=u^2+4u+2, the elementary relative carriers are

    b_N ~ sqrt(2/P(u)) exp[N u(u+1)/(u+2) + u/2 + u^2/4]
    c_N ~ sqrt(2/P(u)) exp[N u(u+1)/(u+2) - u/2 - u^2/4].

Each has relative error O((log N)^4/N). The binary probability has the sharper
exp(-u^2/2-u) carrier, an explicit rational first correction, and an
all-fixed-order exact-saddle quotient algorithm. Its proof uses a standardized
N^epsilon window so that the tails remain negligible relative to the rare
event; a central limit theorem alone would not establish the result.

The exact smooth carrier gives two-ceiling brackets for the ordinary integer
threshold with arbitrary fixed inverse-power accuracy. Elementary seeds for
both thresholds have vanishing absolute error, and all fixed logarithmic
inverse orders are generated recursively. No unconditional exact-ceiling
rule is asserted. The included b_1000 counterexample shows why even a seed
with a tiny positive error can round incorrectly.

Constants and eventual thresholds in asymptotic errors are non-effective in
this proof. Numerical diagnostics are high-precision finite consistency
checks, not interval certificates or proofs of asymptotic remainders.
The expansion order is fixed; complex marks, growing orders, other difference
parameters and full collision-distribution laws are not proved here.

## Contents

- `Report242.pdf`: article
- `article.tex`, `sections/`: complete editable proof and bibliography
- `SOURCES.md`: source attribution, exact indexing and access boundaries
- `COMPUTATION.md`: algorithms, finite verification scopes and limitations
- `code/`: exact and symbolic checks, diagnostics, guards and ZIP replay
- Four JSON receipts in `code/`: deterministic outputs of the checks
- `build.py`: manifest verification, immutable build and archive creation
- `MANIFEST.sha256`: complete inventory of every other package file
- `requirements.txt`: pinned Python dependencies and TeX requirements

The archive contains no third-party paper, private review, research
correspondence, credential, repository history or network dependency.
No upload, publication or external peer review is implied.

## Reproduce

Use Python 3.11 or later with mpmath 1.3.0 and SymPy 1.14.0, and the recorded
pdfTeX/LaTeX toolchain. From the extracted `Report242/` directory:

```sh
python -B -X int_max_str_digits=640 build.py --verify-only
python -B -X int_max_str_digits=640 build.py \
  --output-dir /absolute/existing-parent/new-build
python -B -X int_max_str_digits=640 code/reproduce_zip.py \
  --archive /absolute/existing-parent/new-build/Report242.zip \
  --original-build-dir /absolute/existing-parent/new-build \
  --output-dir /absolute/existing-parent/new-replay
```

Output directories must be new, outside the sources, with existing parents.
They are never reused or merged. The optional report-number argument must
be 242. Build commands perform no network access or publication.

The builder checks the complete manifest, regenerates four receipts, compiles
a temporary TeX copy with a private format and shell escape disabled, and
requires the PDF and receipts to match the frozen originals. It then emits
a deterministic ZIP and a build-check record. Every source tree stays
unchanged; generated files and TeX caches stay outside it.

The replay verifier accepts only the exact package trusted by the running
verifier. It validates the actual ZIP, extracts two independent copies,
rebuilds normally and with `-O`, and compares all seven top-level files
(PDF, ZIP, four receipts and build-check JSON), archive members and metadata,
and complete archive bytes against the original. It verifies that the
trusted tree, both extracted trees and input archive remain unchanged.
Reproducibility on other software versions is not promised.

## Interpretation of the checks

Bounded exact enumeration independently multiplies cell generating
polynomials and checks the closed sums, shifts, transforms, binary products
and residual-cell identities. Symbolic Gaussian contractions check the
first ordinary and binary corrections and the moment/inverse algebra.
The numerical script retains the exact gamma phase at every saddle.
No coefficient is fitted. Explicit exception guards stay active under `-O`.

All Python children explicitly disable bytecode writing and impose the
640-digit decimal conversion cap, which each process also sets internally.
Large integers are hashed as binary bytes rather than printed as enormous
decimal strings. Fixed input ranges and state budgets make verification
bounded. The manifest proves integrity relative to the supplied package,
not authorship, provenance or mathematical correctness.
