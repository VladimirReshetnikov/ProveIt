# A fixed Diophantine encoding of ZFC consistency

This contribution constructs a specific ordinary polynomial `P` with integer
coefficients such that

\[
\mathsf{ZFC}\vdash
\bigl(\nexists\mathbf x\in\mathbb Z_{>0}^{16}:P(\mathbf x)=0\bigr)
\longleftrightarrow\operatorname{Con}(\mathsf{ZFC}).
\]

The principal evaluator has **73 operations: 41 multiplications and 32 additions
or subtractions**, and the polynomial has **exact degree 156**. The package also
provides a seven-equation system, an unrestricted-integer equation, and all 46
equations of an unrestricted-integer quadratic system. The PDF and its TeX source
contain the mathematical proof and explicit formulas.

## Entry points

- **Read:** `zfc_diophantine.pdf` (16 pages) or `zfc_diophantine.tex`.
- **Check everything practical:** `python3 src/verify_all.py`.
- **Rebuild the PDF and run the checks:** `bash build.sh`.
- **Use the 73-operation polynomial:** `data/polynomial73.json`.
- **Use the seven-equation system:** `data/system65.json`.
- **Use all integer variables:** `data/integer44.json`.
- **Use the explicit quadratic equations:** `data/quadratic83.txt` and
  `data/quadratic83.json`.

The scripts use the Python standard library. They were run with Python 3.12.
The PDF uses pdfLaTeX and ordinary TeX Live packages: `amsmath`, `amssymb`,
`amsthm`, `mathtools`, `lmodern`, `geometry`, `booktabs`, `microtype`, `enumitem`,
`listings`, `hyperref`, and `fancyhdr`. No Lean, Rocq, SymPy, or network access is
needed for the packaged finite checks.

## Representations

| Representation | Unknowns and domain | Equations | Exact degree / maximum residual degree | Complete arithmetic count |
|---|---:|---:|---:|---:|
| Scaled polynomial `P` | 16 positive integers | 1 | 156 | 73 = 41M + 32A |
| Unscaled polynomial `U` | 16 positive integers | 1 | 144 | 74 = 42M + 32A |
| Comparison system | 16 positive integers | 7 | 60 | 65 = 35M + 30A |
| Direct sum of squared residuals | 16 positive integers | 1 | 120 | 85 = 42M + 43A |
| Positive-coordinate substitution in `P` | 44 unrestricted integers | 1 | 312 | 171 = 83M + 88A |
| Explicit quadratic system | 83 unrestricted integers | 46 | 2 | Not minimized |
| Sum of its 46 squared residuals | 83 unrestricted integers | 1 | 4 | Not minimized |

Every multiplication by a fixed numeral is charged. Fixed numerals and reuse
of previous registers are free. Coefficient bit complexity and construction
cost are excluded from this arithmetic-circuit metric. Equalities in the
comparison system are counted as equations; subtraction of their right-hand
sides and the sum-of-squares finalizer are fully charged in the SOS evaluator.

No global simplicity or variable-count record is claimed. The construction is
optimized for a short evaluator within the supplied native-compiler framework.
It fixes an ordinary input, so it is not a replacement for the repository's
varying-input universal-polynomial operation frontier.

## What the polynomial is

The positive coordinates are
`J, F, alpha, t, f, h, i, T, s, w, tau, eta, zeta, y, Z, gamma`.
Their exact source names are listed in each JSON packet. Define

\[
\begin{aligned}
q&=(B-1)J+1,& X&=wq,&Y&=sq^3,&E&=XY,\\
k&=\eta+\zeta,&c&=kY+\eta,&a&=E+Y,&H&=4a+3,\\
\Delta&=a^2+H,&D&=X+ac+\gamma H,\\
C&=q-F-Z-\alpha-2d,&W&=C-Z,\\
R&=(q^2-Z-qF)(q^2-1)+(M_C+q\widehat M_F)J,\\
L&=E(kY),&S&=\Delta i^2c^4,&A_0&=\Delta^2i^2c^4,\\
V&=c(Tf-1)-Rf^2.
\end{aligned}
\]

The seven factors are

\[
\begin{aligned}
N_1&=\tau^2-L(L+k),&N_2&=D^2-\Delta c^2,\\
N_0&=3W+1-3W_0,&N_3&=A_0(V^2-y^2)+y^2,\\
N_4&=k-hE-R,&N_5&=(K_0+w)C+q-F-t(q-1),\\
N_6&=f^2-S.
\end{aligned}
\]

Set

\[
U=N_1N_2N_0N_3N_4N_5N_6-1,\qquad P=\Delta U.
\]

The seven-equation version is

\[
W=W_0,\qquad N_1=N_2=N_3=N_4=N_5=N_6=1.
\]

The intermediate letters are polynomial abbreviations, not additional unknowns.
The proof that a product zero forces all seven equalities is part of the paper.
All exponents involving compiler parameters occur only in **fixed coefficients**;
there is no exponent depending on a Diophantine unknown.

## Fixed coefficients

The exact source snapshot is
`cdd582bec13f908df3711fa9e05d1ddac368a5db` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/cdd582bec13f908df3711fa9e05d1ddac368a5db).

The literal K215 transition table is included in `data/k215.tm`. Four additional
initialization states erase the fixed unary input and begin K215 on a blank
tape. The complete normalized table has 219 working states, one absorbing halt,
three tape symbols, and 660 transition rows.

The exact count and layout calculations give

\[
\begin{aligned}
\#\text{tiles}&=669,\\
\#\text{allowed windows}&=47353022820782362885779,\\
b&=5^{35},\qquad L_*=5^{36},\qquad d=5^{71},\\
B&=2^{5^{71}},\qquad W_0=2^{5^{35}+2\cdot5^{71}}.
\end{aligned}
\]

The coefficient ports have these exact meanings:

| Source port | Mathematical coefficient |
|---|---|
| `Bm1` | `B - 1` |
| `Kconstant` | `K_0 = D_C + B D_R` |
| `twice_cell_bits` | `2d` |
| `MC` | Native mask `M_C` |
| `MF` | **Shifted** mask `M_F + B - 1` |
| `input_unit_constant` | `1 - 3W_0`, for the product evaluators |
| `W0` | `W_0`, for the seven comparisons and quadratic system |

The six ports used in any one representation are fixed integers. The shift in
`MF` must be retained.

`src/k215_constants.py`, Section 4 of the paper, and
`provenance/COEFFICIENT_RECIPE.md` specify every finite predicate, order,
sum, and arithmetic operation defining the remaining coefficients. This is a
closed coefficient specification tied to the literal machine. It leaves no
unspecified machine index, unknown halting time, or unbounded search.

**Not materialized:** the enormous ordered window list, sparse coefficient
arrays, and expanded decimal or hexadecimal numerals. The default generator
computes the exact scalar manifest without enumerating the windows. Its
`--compile-sparse` and `--materialize` modes implement the complete finite
construction but are astronomically expensive for K215 and are not part of
the reproducibility commands.

## Why the reduction works

The inherited native parent already recognizes the chosen machine's ordinary
input. The new reduction fixes that input and removes its Pell input decoder.
The factor `N_0 = 3W + 1 - 3W_0` must be a unit when the full product is one.
Since it is congruent to one modulo three, it cannot be minus one. Thus it
forces `W = W_0` using two arithmetic operations.

That observation alone is not enough: the omitted input witnesses must be
recoverable. The proof establishes positivity of the packed index before any
decoding, restores the auxiliary quotients, invokes the precise local Pell
rank and step-down lemmas, proves `X = 2^R` without the deleted input theorem,
and reconstructs the three removed positive witnesses. This gives both
directions of the zero-set correspondence with the parent at input one.
The small initializer then connects the compiled machine to literal K215.
The inherited K215 calibration connects blank halting to a finite ZFC refutation.

Each argument is ordinary mathematics formalizable in ZFC. Their composition
gives the requested internal equivalence; it does not assume `Con(ZFC)`.
Under consistency the resulting nonexistence statement is not provable in
ZFC. Full two-sided unprovability is not asserted from consistency alone.

## Integer domains

The 16-variable polynomial must not be used unchanged over all integers.
The scaling factor `Delta` can vanish outside the intended positive domain.

For the 44-variable equation, the two coordinates appearing only squared,
`tau_root` and `y_aux`, can be signed. Each of the other fourteen coordinates
is replaced by `1 + a^2 + b^2 + c(c+1)`, which parametrizes exactly the positive
integers. This gives the explicit circuit in `data/integer44.json`.

For the quadratic system, affine gates are inlined and the seven comparison
equations are solved using pivots with coefficient one or minus one. The 32
remaining product equations are quadratic. Fourteen equations
`4v - 3 = a_v^2 + b_v^2 + c_v^2` enforce positivity, using the three-square
theorem. The result is precisely 46 quadratics in 83 unrestricted integers.
The sum of their squares is a single quartic with the same solutions.

## Verification and proof status

The completed receipt is `verification/full.json`. The practical checks include:

- Authentication of the literal K215 table, all 430 inherited transitions,
  all 660 normalized rows, input erasure, and 120,000 paired simulation steps.
- An accepting two-sided helical tableau fixture, both overlap directions,
  exact marker separation, and five materialized small compiler instances.
- A factored window-count check against 209,952 weighted cross assignments
  for an 18-tile fixture.
- Exact sparse-layout comparisons against two authenticated upstream compiler
  functions, including both optional-correction branches.
- Complete circuit closure, liveness, operation ledgers, 80 exact arithmetic
  fixtures, and coefficient diagnostics for degrees 144, 156, 120, and 312.
- Exact symbolic substitution through all 32 product equations and seven
  comparisons, equality of all 46 printed residuals to their JSON forms,
  and the coefficient-one witness for exact quartic degree.

These finite checks do not decide whether K215 halts. The unbounded equivalence
is established by the mathematical proof, which relies on the cited inherited
Pell and compiler theorems. The leading-form proof establishes the exact degree
uniformly; finite-field diagnostics corroborate it.

Separate derivation and review passes within this research collaboration checked
the new mathematical steps. They are not an external human endorsement. The
new fixed-input theorem and direct normalization have **not** been formalized
as new Lean or Rocq endpoints, and the inherited full proof-assistant dependency
trees were not rebuilt. Existing upstream endpoints remain precisely attributed.

## File organization and incorporation

| Location | Contents |
|---|---|
| `zfc_diophantine.tex`, `.pdf` | Complete paper and explicit quadratic appendix |
| `data/` | Literal machine, normalized machine, exact scalar manifest, arithmetic circuits, 46 quadratic equations |
| `src/` | Standard-library generators and practical verification entry points |
| `src/upstream/` | Exact copies of the two ancestor compiler sources used by the transcription audit |
| `verification/` | Actual finite-check receipts |
| `provenance/` | New proof reviews, normalizer and coefficient notes, upstream source manifest |
| `provenance/upstream/` | Immediate inherited mathematical notes and K215 attribution/verification overview |
| `SHA256SUMS` | Integrity manifest for the delivered files |

The folder is self-contained for its Python checks and PDF build. It can be
placed under a new research directory in `Computability/HilbertTenthProblem/`
without changing its relative paths. The copied source notes preserve the
upstream text; their internal relative links refer to their original repository
locations, recorded in `provenance/upstream_sources.json`.

The repository's MIT No Attribution license is included. The K215 notice retains
its inherited attribution and third-party licensing boundaries; the inclusion
of that notice does not relicense any inherited components.

