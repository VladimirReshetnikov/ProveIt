# Fixed-base modular Diophantine consistency

Research contribution for **ProveIt**, 25 October 2026.

This packet gives two completely specified quartic polynomials over the
unrestricted integers. The accompanying ordinary proof, composed with the
retained numerical-calculus calibration, establishes in ZFC:

\[
\neg\exists\boldsymbol z\,P(\boldsymbol z)=0
\quad\Longleftrightarrow\quad
\operatorname{Con}(\mathrm{ZFC}).
\]

Equivalently, an integer zero exists exactly when a finite syntactic ZFC
refutation exists. This statement does not assume or prove consistency.

## Delivered equations

| Profile | Integer variables | Quadratic residuals | Degree | Collected monomials | Coefficient height | Largest residual coefficient |
|---|---:|---:|---:|---:|---:|---:|
| Balanced principal | **230** | **176** | **4** | **4,482** | **7,968** | **64** |
| Compact companion | **229** | **175** | **4** | **12,006** | **7,968** | **64** |

The principal equation is
\[
P(z_0,\ldots,z_{229})=\sum_{i=0}^{175}R_i(\boldsymbol z)^2=0.
\]
The companion is
\[
Q(w_0,\ldots,w_{228})=\sum_{i=0}^{174}S_i(\boldsymbol w)^2=0.
\]
All coordinates are independently quantified over **all integers**.
Every residual is quadratic with literal integer coefficients. There are
no unspecified constants, variable exponents, factorials, binomial
operations, or extra quantified symbols in these two polynomial lists.

The report prints all 351 residuals. Each equation directory also
contains its entire collected quartic, not merely a generator or digest.

## Start here

- [ConZFC_Fixed_Base_Modular.pdf](ConZFC_Fixed_Base_Modular.pdf) — full
  report, ordinary proof, comparison, verification account, and both
  complete residual lists.
- [ConZFC_Fixed_Base_Modular.tex](ConZFC_Fixed_Base_Modular.tex) —
  standalone TeX source with every generated input embedded.
- [equations/balanced](equations/balanced) — the 230-variable equation.
- [equations/compact](equations/compact) — the 229-variable companion.
- [verify.py](verify.py) — independent checks and reconstruction.
- [proofs](proofs) — component proofs, reviews, and review responses.
- [provenance/SOURCE_LEDGER.json](provenance/SOURCE_LEDGER.json) —
  pinned commit, archive hashes, logical interfaces, and attribution.

## What changes mathematically

### One binomial serves two purposes

For the cofinal proof horizon \(t=16+h^2\), use
\[
R=16^t,\qquad B=\binom{R+t}{t}.
\]
The elementary estimate
\[
\operatorname{lcm}(1,\ldots,t)\le4^{t-1}
\]
lets this fixed-base radius satisfy the predecessor's prime-power row
selector theorem. At the same time,
\[
B>(t+1)^t
\]
lets the **same \(B\)** separate Horn-label multiplicities through weights
\(1+jB\). A separate variable-base growth power is unnecessary.
The beta spacing is \(y=RB(2v+1)^2\).

### Signed modular numerators compose with the compact Pell interface

Eleven numerator values are needed only modulo \(Nq^x\). They are supplied
by signed Pell evaluations
\[
\mu_n=X_n(A)+(q+1-A)Y_n(A)
\]
and one common-root condition. Six power requests remain exact:
\[
R=16^t,\quad N=B^x,\quad q=(BH)^x,\quad
D_t=q^t,\quad D_y=q^{y+1},\quad M=q^x.
\]
The successor denominator is \(qD_t\).

The modular numerator/common-root method is **inherited**, not claimed
as a new invention. The new composition uses a squared majorant for
signed CRT representatives and derives positivity in a noncircular
order from existing requests. The proof explicitly handles negative
upper binomial arguments and the possible temporary case \(B=1\).

### A cofinal Pell center needs only two squares

The new center is
\[
A=L^2+u^2+v^2,
\]
instead of a universal ternary slack. An arbitrary fixed frame point
does not suffice. The proof chooses an **odd multiple of the Pell
frame index** using the odd part of a finite quadratic-ring unit order.
This makes every local correction a unit, zero, or a residue of even
prime-adic valuation. Each is a sum of two squares modulo the relevant
odd prime power. CRT and unrestricted lifts make \(A\) arbitrarily
large in the required congruence class.

The proof handles ramified primes and preserves the frame's odd
ordinate quotient. No order computation or additional unknown is
inserted into the polynomial: this is a completeness argument for
jointly choosing existing witnesses.

The negative control \(W=4,\ q=3,\ \Omega=9,\ L=4801\) is included:
the required correction at this fixed frame is \(3\bmod9\), which is
not a sum of two squares. The cofinal choice is essential.

## Comparison and scope

The source snapshot is ProveIt commit

    b7e35224c04fe1031c0a53f80a395e9b32205022

including all eight incoming archives present there. Compared with the
immediate factorial-free predecessor:

| Matched profile | Parent variables / monomials | New variables / monomials | Height |
|---|---:|---:|---:|
| Sparse | 242 / 5,018 | **230 / 4,482** | 7,968 in both |
| Compact | 241 / 12,774 | **229 / 12,006** | 7,968 in both |

The incoming shared-error equation has 240 variables, 21,482 monomials,
and lower height 6,144. The normalized-residue balanced equation has
244 variables, 5,212 monomials, and height 3,968. These are tradeoffs
rather than uniformly dominated measures.

The repository also contains far fewer-variable constructions with
different degree or fixed-coefficient costs, including a 37-integer
quartic. This packet does **not** claim a global simplicity minimum or
a worldwide priority result. Its contribution is to the direct
proof-calculus family with modest literal coefficients. It uses
neither K215 nor an instance of Jones's universal equation.

The new ordinary proofs were separately reviewed within the AI-assisted
workflow. That is not outside human refereeing. The retained Lean
calibrations are included, but their full transitive development was
not freshly rebuilt. No new end-to-end Lean/Rocq formalization is claimed.

## Verification

Requires Python **3.10 or later**, standard library only:

    python3 -B verify.py
    python3 -O -B verify.py

By default these commands change no delivered file; temporary
reconstructions are discarded. To save a receipt, pass the option
--receipt followed by a destination JSON path.

The checker covers:

- Every fixed-base source row and all 18 request-manifest ports.
- Six remaining exact powers, eleven modular definitions, fourteen
  principal signed Pell pairs, and the shared modulus.
- The five removed frame atoms and the two-square center change.
- Eighteen independently checked Horn factoring edits.
- All 208 integral monic restorations and 69 coordinate translations.
- Both final affine projections and every collected quartic coefficient.
- Seven deliberate corruption controls.
- The signed derived-label bound from its actual 91-gate ancestor graph.
- Finite arithmetic regressions, including 2,210 two-square completions
  and 3,128 local prime-power cases.
- Byte-identical reproduction of all **41** new stage/endpoint JSON files.
- Both readable residual lists, variable maps, report inputs, and the
  retained predecessor's own verification.

Finite checks validate finite artifacts and detect errors. They do not
replace the unbounded soundness/completeness proofs.

For an isolated persistent rebuild:

    python3 -B reproduce.py --output /path/to/new-empty-directory

For a quick finite audit without rebuilding the retained predecessor:

    python3 -B verify.py --skip-parent --skip-rebuild

The receipt explicitly records skipped work. Use --skip-manifest only
while intentionally editing a working copy. The release manifest is a
local checksum inventory, not a signature.

## Data format

Each equation JSON declares its domain, ordered coordinates, and
residual list. The sparse term [7, [2, 5]] means \(7z_2z_5\), while
[7, []] means the constant 7. Repeated indices denote powers. The
polynomial is the sum of all residual squares. The expanded-polynomial
JSON uses the same convention for the collected quartic. The TSV maps
give inherited coordinate names; printed coordinates use zero-based
indices.

Source and transformation certificates record integral inverses for
eliminated coordinates. No division by a potentially nonunit coefficient
is silently performed.

## Building the report

An ordinary TeX Live installation with AMS packages and Latin Modern
fonts suffices:

    sh build_report.sh

The script checks the readable exports and runs pdflatex twice.
The standalone TeX file may also be compiled directly. The editable
article body is report/report.tex; after intentional changes, run:

    python3 -B code/report_inputs.py

This regenerates the standalone source. PDF metadata may depend on the
TeX installation; exact polynomial data do not.

## Integration

See [INTEGRATION.md](INTEGRATION.md) for placement and review priorities.
The complete immediate predecessor remains under upstream/factorial_free,
with its own notices, provenance, checksums, and logical source interfaces.

The packet uses the repository's **MIT No Attribution** license. See
[LICENSE](LICENSE) and [NOTICE.md](NOTICE.md).
