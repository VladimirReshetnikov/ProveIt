# Report 169: exact packed-matrix companion

This offline companion counts matrices with exactly **n ordered nonzero rows**, any number of **ordered nonzero columns**, nonnegative integer entries, and total entry sum **2n**. Rows and columns are not identified under permutation. The empty matrix has count 1. The counts are OEIS A261784.

The default programs use only the Python standard library. Python **3.10 or later** on a POSIX system (such as Linux or macOS) is required for the complete test and output-writing workflow; the supplied outputs and tests were checked with Python 3.12. All computation commands are offline: they make no network requests, install no packages, and modify no remote resource.

## Quick start

Run these commands from the `companion` directory:

```sh
python -m unittest -v
python -O -m unittest -v
python run_companion.py count 14
python run_companion.py marked 3
python run_companion.py coefficients --q 3/4 --R 2/3
python run_companion.py diagnostics 10 20 50 100 --digits 60
python run_companion.py generate --output reproduced
```

`generate` creates a **new** directory. Its parent must already exist, and the requested output directory must not exist. Existing directories, files, and symlinks are rejected; existing outputs are never overwritten. Parent-traversal (`..`) output paths and symlink ancestors are rejected. The writer pins POSIX directory descriptors and opens output files exclusively with `O_NOFOLLOW`, so it does not follow a symlink swapped into a checked ancestor. Unsupported platforms fail closed for output generation; the arithmetic itself uses portable standard-library operations. Use a different output name for another run. A filesystem error during writing can leave a partial *new* directory, which can be inspected; it never authorizes replacement of existing data.

The five files in `reproduced` are byte-for-byte reproductions of `examples` with the default 60-digit setting. There are no wall-clock timestamps, timing results, random seeds, or machine-specific paths in those JSON files. To check reproduction without additional dependencies:

```sh
python -c "from pathlib import Path; a=Path('examples'); b=Path('reproduced'); names=sorted(p.name for p in a.iterdir()); ok=names==sorted(p.name for p in b.iterdir()) and all((a/n).read_bytes()==(b/n).read_bytes() for n in names); print('MATCH' if ok else 'MISMATCH'); raise SystemExit(0 if ok else 1)"
```

All automated checks remain active under `python -O`. No validation or test relies on Python `assert` statements. Invalid command-line inputs produce a concise error and exit status 2. Mathematical inconsistencies likewise fail rather than silently returning a rounded integer.

## Exact counts: independent routes

`count_stirling(n)` implements

\[
 a_n=\frac{n!}{(2n)!}\sum_{j=n}^{2n}[2n,j]\,{j\brace n}\,B_j,
\]

where the two Stirling families and the ordered Bell numbers are computed by exact integer recurrences. The final division is checked for zero remainder.

`count_inclusion(n)` independently counts sequences of nonzero columns, then removes empty rows by inclusion-exclusion. For `r` allowed rows, a column of sum `j` has `binomial(r+j-1,j)` choices. Thus

\[
 F_r(0)=1,\quad F_r(N)=\sum_{j=1}^{N}\binom{r+j-1}{j}F_r(N-j),
 \qquad a_n=\sum_{r=0}^{n}(-1)^{n-r}\binom nr F_r(2n).
\]

This second route does not use Stirling numbers or Bell numbers. Both reproduce the 15 frozen OEIS terms, with indices 0 through 14. The generated bundle additionally compares both routes at n=20,50,100.

```sh
python run_companion.py count 100 --method both
python run_companion.py count 200 --method stirling
```

Large exact integers are encoded as **decimal strings** in JSON so consumers using binary64 numbers cannot silently round them. Base-10 chunk conversion supports counts beyond Python 3.11's default integer-to-string digit guard without changing that global safeguard.

The n=800 calculation is an optional larger run, outside the default bundle. It uses the Stirling route only. A 60-digit n=800 diagnostic took about 26 seconds in one Python 3.12 run; runtime is machine-dependent and may be longer. For example:

```sh
python run_companion.py count 800 --method stirling
python run_companion.py diagnostics 800 --digits 60 --output large_reproduced
```

The default run remains n<=100. Inclusion-exclusion is deliberately capped at n=100. The optional command reproduces `optional_large_run/diagnostics_uncertified.json` and its manifest in a new directory.

## Exact marked polynomials

The marker `J` counts cells whose entry is at least 2; `K` counts nonzero columns. A record `{J, K, count}` is the coefficient of `u^J v^K`.

`marked_transform` computes the finite exact transform using

\[
 w(z,u)=-\log(1-z)+\log(1+(u-1)z^2),\qquad
 B_j(v)=\sum_k k!{j\brace k}v^k.
\]

Every rational intermediate coefficient uses `fractions.Fraction`. Final coefficients are checked for nonnegative integrality.

`marked_enumeration` independently enumerates ordered sequences of nonzero column vectors, tracking total mass, a row-coverage bitmask, and the number of repeated cells. Vectors with equal state contributions are aggregated with exact multiplicities; no generating-function transform is used. The supplied outputs compare the entire polynomial for n=0,1,2,3,4, not just its value at u=v=1. Each record also gives exact mean J, mean K, and variance K as rational strings.

For example, `A_1(u,v)=uv+v^2`. The sum of the coefficients of `A_4` is 893490.

## C0 through C3: exact algebra and decimal values

The expansion is normalized as

\[
 a_n\sim C d^n (n!)^2/n\;\sum_{j\ge0} C_j n^{-j},\qquad C_0=1.
\]

Here `rho=log(2)`, `q=t/2` is the root in `(1/2,1)` of `-log(1-q)=2q`, and

\[
 C=\frac{e^{\rho q}}{4\pi\rho\sqrt{2q-1}},\qquad
 d=\frac{1}{\rho^2 q(1-q)}.
\]

`frozen/coefficients_C0_C3.json` contains exact rational functions, not fitted decimal constants. A numerator item `[c,i,j]` means `c*q^i*R^j`. The denominator is `denominator_scale*(2*q-1)^denominator_power`. For the unmarked sequence, substitute `R=rho`. `coefficient_formulas.txt` gives the same expressions in readable text.

The finite coefficient calculator uses the Morse/Lagrange formula in Report 169. In the coordinate `x=Q/q-1`, let `b=(2q-1)/(1-q)`, `f(x)=Phi(q(1+x))-Phi(q)`, `S(x)=2f(x)/(b*x^2)`, and `F_j(x)=A(q(1+x))*P_j(q(1+x))/(A(q)*(1+x))`. It computes

\[
 C_m=\sum_{j=0}^{m}(-1)^{m-j}(2(m-j)-1)!!\,b^{-(m-j)}
 [x^{2(m-j)}]F_j(x)S(x)^{-(m-j)-1/2}.
\]

The implementation retains only degree 6, enough for C0–C3. The corrections are

\[
 H_1=Q^2/(12(1-Q))-RQ/2-(RQ)^2/12-1/12,\quad H_2=-(RQ)^2/24,
\]
\[
 H_3=-Q^3((1-Q)^{-3}-1)/360+(RQ)^4/1440+1/360,
\]

with `P_0=1`, `P_1=H_1`, `P_2=H_2+H_1^2/2`, and `P_3=H_3+H_1*H_2+H_1^3/6`. The phase uses `Phi(Q)=1+(1-Q)log(1-Q)/Q-log(Q)`, and `A(Q)=(1-Q)^(-1/2)exp(RQ)`. Saddle substitution eliminates `log(1-q)` as `-2q`.

The standard-library tests compare this calculation with the frozen rational functions at 12 exact rational pairs `(q,R)`. **These finite specializations alone are not a proof of a rational-function identity.** They are regression checks. Inputs to the `coefficients` command are rational specializations of these formulas; they are not exact representations of the transcendental saddle parameters.

### Optional full symbolic identity check

`verify_symbolic.py` runs the same finite coefficient prescription over the exact field `Q(q,R)` and checks equality to all four frozen expressions. It also compares C1 with the displayed formula in `t=2q`, separately written in the verifier. SymPy is isolated to this optional script; it is never imported by the default programs or tests.

If SymPy is already installed:

```sh
python verify_symbolic.py
python -O verify_symbolic.py
python verify_symbolic.py --output symbolic_reproduced
```

The last command writes to a new directory under the same no-clobber rule. The supplied result is in `symbolic_checks/symbolic_checks.json`. It was obtained with SymPy 1.14.0. To install the pinned optional packages yourself when network access is available, use:

```sh
python -m pip install -r requirements-optional.txt
```

Installation is not part of any computation command. A missing optional dependency produces a clear error. The saved symbolic output states the package version; a different SymPy version may change that metadata even when the identities agree.

## Numerical diagnostics are uncertified

`diagnostics_uncertified.json` recomputes exact integer counts, then evaluates constants and normalized residuals using `decimal.Decimal`. It uses a bracketed numerical root calculation for q, Gauss–Legendre iteration for pi, and 30 guard digits. C0–C3 are computed both by the finite coefficient prescription and by evaluating the exact frozen expressions; these rounded results are cross-checked.

Every numerical output is explicitly labeled **UNCERTIFIED**. There is no interval arithmetic, explicit error enclosure, certified last digit, or threshold certificate. The tests comparing reference digits are numerical regression checks, not rigorous numerical bounds. The asymptotic remainder theorem must be justified by the report's analysis, not by these residuals. No convergent-series or optimal-truncation claim is made.

For retained order `m`, the recorded residual is

\[
 n^{m+1}\left(\frac{a_n}{C d^n(n!)^2/n}-\sum_{j=0}^{m}C_j/n^j\right).
\]

### Smooth inverse diagnostics

Each numerical record also reports the error at `x=a_n` of the leading Lambert formula and its first two corrections. With all normalization constants retained, the calculator uses

\[
 Y=(\log x-\log(2\pi C))/2,\quad W=W_0((\sqrt d/e)Y),\quad v=Y/W,
\]

\[
 h_1=C_1+1/6,\quad h_2=C_2-C_1^2/2,\quad L=1+W,
\]

then compares `v`, `v-h_1/(2vL)`, and `v-h_1/(2vL)-h_2/(2v^2L)` with n. W is evaluated by bounded Newton iteration on its positive real branch using guarded Decimal arithmetic. The first- and second-correction errors at n=800 are approximately `-7.68077637e-10` and `2.45521081e-12`.

These are **uncertified smooth inverse diagnostics**. They provide no exact integer inverse, no ceiling rule near sequence thresholds, and no explicit numerical remainder certificate.

## Deliberate resource bounds

| Operation | Accepted range |
|---|---|
| Exact Stirling count | integer n=0..800 |
| Independent inclusion-exclusion count | integer n=0..100 |
| Exact marked transform | integer n=0..8 |
| Direct marked enumeration | integer n=0..4 |
| Diagnostic list | 1..12 distinct integers, each n=1..800 |
| Decimal output precision | 30..160 significant digits |
| Coefficient order | C0..C3 only |
| Rational coefficient arguments | 1/2<q<1, 0<R<=2, at most 256-bit numerator/denominator |

Booleans, floats, strings, negative indices, and out-of-range indices are rejected by integer APIs. The coefficient API requires `Fraction` arguments. Command-line rational arguments accept only an integer or `p/q`, with at most 77 decimal digits per part; zero denominators and oversized values are rejected. These finite limits protect against accidental unbounded work. The companion does not implement arbitrary-order coefficients, certified inversion, or a global integer-threshold selector.

## File map and provenance

- `packed_matrix.py`: standard-library exact arithmetic, bounded generators, decimal diagnostics, exclusive JSON writer
- `run_companion.py`: command-line interface
- `test_companion.py`: 19 test cases, including input failures and no-clobber behavior
- `verify_symbolic.py`: optional full rational-function identity check
- `frozen/oeis_A261784.json`: 15 terms, offset, definition, source URL and retrieval date
- `frozen/coefficients_C0_C3.json`: exact sparse rational-function encoding
- `coefficient_formulas.txt`: readable exact expressions
- `examples/`: deterministic exact and uncertified numerical JSON outputs with SHA-256 manifest
- `symbolic_checks/`: exact symbolic equality results with SHA-256 manifest
- `optional_large_run/`: n=800 uncertified numerical diagnostics and the 4838-digit exact count, with SHA-256 manifest
- `provenance.json`: source locations and attribution

The exact transform is credited to E. Munarini, M. Poneti and S. Rinaldi, **Matrix Compositions**, *Journal of Integer Sequences* 12 (2009), Article 09.4.8, Section 7, Proposition 29, equation (36): https://cs.uwaterloo.ca/journals/JIS/VOL12/Rinaldi/rinaldi.pdf

The frozen prefix and existing leading equivalent are from https://oeis.org/A261784 (retrieved 3 October 2026). The leading equivalent retains OEIS's attribution to Václav Kotěšovec, 18 February 2017, updated 20 April 2024. The present companion's finite checks do not establish worldwide novelty or certify analytic remainder bounds. See Report 169 for the fixed-order and marked arguments and their literature context.
