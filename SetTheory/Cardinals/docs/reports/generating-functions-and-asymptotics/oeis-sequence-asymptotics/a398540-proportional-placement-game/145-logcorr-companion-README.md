# Report145: exact algebra companion

This small, standard-library-only Python package independently checks exact
algebra used in the full second-order theorem for the A398540 placement
recurrence:

\[
\frac{W_n}{A\sqrt n\,r_*^n}
=1+\frac1{4n}-\frac7{540}\frac{\log n}{n^2}
+\frac{B_2}{n^2}+o(n^{-2}).
\]

The report proves existence of the finite constant \(B_2\), gives its
absolutely convergent-series representation, and proves eventual strict
decrease of the ratios \(W_{n+1}/W_n\).

**Scope:** successful finite computation does not certify those analytic
conclusions, their hypotheses, convergence, uniform error estimates, an
effective monotonicity threshold, or any decimal digits of \(B_2\) or
\(r_*\). Those belong to the report's proof or remain outside its stated
scope. This package checks exact algebra, with three inverse-asymptotic
coefficients explicitly declared as analytic inputs. No recurrence numerics,
floating-point arithmetic, external libraries, downloads, or network access
are used here.

## Run

Python 3.9 or later is sufficient. From this directory:

```sh
python -I checks.py
python -I -O checks.py
python -I test_checks.py
python -I -O test_checks.py
```

`-I` enables Python's isolated mode; `-O` disables Python assertion statements.
All checks instead raise explicit exceptions, so optimization cannot disable
them. The test suite requires isolated mode and launches additional isolated
CLI checks in the matching optimization mode.

To create a **new** deterministic JSON receipt:

```sh
python -I checks.py --receipt new-receipt.json
```

Receipt creation requires POSIX directory-descriptor support. Existing files,
directories, target symlinks, dangling symlinks, and symlink parent directories
are refused. Parent directories must already exist. Paths with `..`, a
trailing separator, or NUL are rejected. Traversal uses directory descriptors
and `O_NOFOLLOW`; creation uses `O_EXCL`, not a check-then-overwrite sequence.
Without `--receipt`, verification only prints its receipt to standard output.
Do not redirect shell output over an existing file you want to preserve: shell
redirection is outside these guards.

## Independently recomputed values

Integrating rational polynomials exactly gives

\[
\int_0^1 v^2\,dv=\int_0^1(1-v)^2\,dv=\frac13,\qquad
\int_0^1v^2(1-v)^2\,dv=\frac1{30},
\]

and hence
\(\operatorname{Cov}(v^2,(1-v)^2)=-7/90\). Multiplying the two
\(-1/2\) Taylor coefficients gives the normalized covariance \(-7/360\).

The exact coefficient chain is

\[
\begin{aligned}
p&=\tfrac12-\tfrac1{12}-\tfrac16=\tfrac14,& d&=-p=-\tfrac14,\\
q&=-1+\tfrac1{12}+\tfrac12=-\tfrac5{12},&
s&=p^2+pq-\tfrac7{360}=-\tfrac{11}{180},\\
e_{\log}&=4pd+2qd+2s=-\tfrac{59}{360},&
z_{\log}&=2d^2=\tfrac18,\\
h_{\log}&=e_{\log}+z_{\log}=-\tfrac7{180}.&&
\end{aligned}
\]

The final first correction is \(d+1/2=1/4\), and the logarithmic
coefficient is \(h_{\log}/3=-7/540\). The analytic inverse-action estimates
that identify \(d=-p\) and multiply the logarithmic-over-index term by \(1/3\)
are proof inputs, not consequences of testing finitely many values.

## Full second-order constant

The program computes the following second coefficients from exact Taylor
coefficient arithmetic and polynomial integration:

\[
A_{\mathrm{second}}=-\frac{47}{288},\quad
I_{\mathrm{second}}=\frac{13}{120},\quad
b_{\mathrm{second}}=-\frac{179}{1440},\quad
H_{\mathrm{second}}=\frac{217}{288},\quad
a_{\mathrm{second}}=-\frac{269}{1440},\quad
D_{\mathrm{first}}=-\frac{11}{180}.
\]

For example, the \(I\) coefficient is
\(\int_0^1(v^3/3+v^4/8)\,dv\), and the boundary derivative coefficient is
\(-\tfrac12[(5/12)(1/3)-(1/2)(1/30)]\). Their uniform analytic
remainders and the boundary limit are established in the report, not here.

Treating \(\gamma,S_a,S_y,K,Q\) as formal symbols, the exact assembly gives

\[
h_C=\frac{461}{480}-\frac7{180}\gamma
-\frac12S_a-\frac56S_y-\frac{11}{90}K+2Q.
\]

The symbols are Euler's constant and the four absolutely convergent sums
defined in the report. The verifier does not evaluate those sums or certify
their convergence.

The three **declared analytic inputs** are the constant coefficients in

\[
\begin{aligned}
(T\ell)_n&=-\frac1{2n}+\frac1{6n^2}+O(n^{-3}),\\
(Tg)_n&=\frac{\log n}{3n^2}-\frac2{9n^2}+o(n^{-2}),\\
(Tw)_n&=\frac1{3n^2}+o(n^{-2}),
\end{aligned}
\]

where \(\ell_k=\log(k+1)\), \(g_k=\log(k+1)/(k+1)\), and
\(w_k=1/(k+1)\). Their rational values \(1/6,-2/9,1/3\) and their
subsequent arithmetic are checked. The asymptotic identities themselves are
not computationally certified.

Retaining the index-shift contribution and the normalization shift
\(d/2-1/8=-1/4\), the program derives

\[
\begin{aligned}
B_2&=h_C/3-1/3-2h_{\log}/9\\
&=-\frac{59}{12960}-\frac7{540}\gamma
-\frac16S_a-\frac5{18}S_y-\frac{11}{270}K+\frac23Q.
\end{aligned}
\]

The reported rational part \(-59/12960\) is not the numerical value of
\(B_2\). All six affine coefficients of both expressions are checked
separately against the closed fixture.
Here the companion symbol and fixture key `K` mean the report's unshifted
\(K_1=\sum_{i\ge1}y_i/i\), not the earlier shifted sum in Section 4.
The companion `Q` means the report's \(\mathcal Q\).

## Rational identities for the critical inverse

The operator in the report is

\[
(Th)_n=\frac{h_{n-1}}{n+2}
-2(n+1)\sum_{k\ge n}\frac{h_k}{(k+1)(k+2)(k+3)},\quad n\ge1.
\]

`checks.py` implements exact rational functions in the formal variable \(n\).
It checks identities by polynomial cross multiplication, not by evaluation
at a finite list of integers. Its three telescoping differences yield

\[
\begin{aligned}
\sum_{k\ge n}\frac1{(k+1)(k+2)(k+3)}
  &=\frac1{2(n+1)(n+2)},\\
\sum_{k\ge n}\frac{k+1}{(k+1)(k+2)(k+3)}
  &=\frac1{n+2},\\
\sum_{k\ge n}\frac1{(k+1)(k+2)(k+3)(k+4)}
  &=\frac1{3(n+1)(n+2)(n+3)}.
\end{aligned}
\]

The corresponding terminal rational terms tend to zero. These telescopes
give the checked exact forcing identities

\[
T(1)=0,\qquad T(k+1)=-1,\qquad
T\!\left(\frac1{k+4}\right)_n=\frac1{3(n+2)(n+3)}.
\]

Three additional coefficient identities check the substitution of the
operator formula into

\[
(n+1)y_{n+1}-(n+2)y_n=h_n-h_{n-1}.
\]

This recurrence identity does not select the critical boundary condition;
that analytic step remains in the report.

## Formal inverse residual

Write \(b=1/4\), \(c=-7/540\), \(t=1/x\), \(\ell=\log x\),
\(u=1/\lambda\), and \(k=B_2-b^2/2=B_2-1/32\). Let

\[
f_0(x)=\lambda x-\tfrac12\log x-\log A,\qquad
h(x)=b/x+[c\log(x)+k]/x^2,\qquad
\Delta=\frac{h(x)}{\lambda-1/(2x)}.
\]

Truncated formal polynomial arithmetic, treating \(\ell\), \(u\), and
the arbitrary \(k\) as symbols, independently expands
\((f_0-h)(x+\Delta)-f_0(x)\) through degree four in \(t\):

\[
\frac{u}{16}t^3+
\left(\frac{7u}{2160}-\frac{7u\ell}{720}
+\frac{3u^2}{64}+\frac{3uk}{4}\right)t^4.
\]

There are no degree-one or degree-two terms. This is a formal coefficient
check, with all omitted monomials having degree at least five in \(t\).
It does not compute a Lambert W value, certify an effective error bound, or
justify a ceiling operation. The supplement's analytic argument provides
the ceiling-safe inverse conclusion.

## Ratio coefficients

Formal substitution of \(t/(1+t)\) for \(1/(n+1)\) and
\(\ell+\log(1+t)\) for \(\log(n+1)\) checks cancellation of the symbolic
second constant and logarithm at order \(t^2\). Multiplication by
\(\sqrt{1+t}\) gives

\[
\frac{W_{n+1}}{r_*W_n}
=1+\frac1{2n}-\frac3{8n^2}+o(n^{-2}),\qquad
\frac{\rho_{n+1}-\rho_n}{r_*}
=-\frac1{2n^2}+o(n^{-2}),
\]

where \(\rho_n=W_{n+1}/W_n\). The exact formal coefficients
\(1/2,-3/8,-1/2\) are checked. The report's little-o bounds justify the
analytic difference and eventual strict decrease. The code does not
differentiate an unspecified remainder or certify monotonicity at every
finite index, an onset, or a ratio coefficient at order \(n^{-3}\log n\).

## Fixtures, tests, and receipts

- `fixture.json` is a closed version-2 expected-value fixture, separate from the code
- `checks.py` recomputes values before comparing with the fixture
- `test_checks.py` mutates every rational value and tests schema/output guards
- `receipt.json` records the successful exact check
- `tests-normal.json` and `tests-optimized.json` record the two isolated suites

Every object has an exact key set. Integer positions reject booleans,
floats, and strings. Fractions require positive denominators and coprime
numerator/denominator pairs; zero is uniquely `0/1`. Duplicate JSON keys,
nonfinite values, decimal JSON numbers, missing/extra fields, unsorted or
duplicate inverse terms, zero inverse terms, and out-of-range exponents are
rejected. A structurally valid fixture with changed mathematics is also
rejected. Receipts use a SHA-256 of canonicalized fixture JSON and contain no
timestamp, machine identifier, or absolute path.

The delivered isolated normal and optimized suites each pass 1,142 cases:
80 semantic mutations, 1,044 structural rejections, 12 output-guard cases,
four CLI checks, and two positive verification cases. The exact verification
receipt is byte-for-byte identical under normal Python and `-O`; the two
test receipts differ only in their optimization flag.

The verifier does not claim that these tests prove its software correct.
They provide a reproducible exact arithmetic audit with explicit negative
cases and a deliberately narrow mathematical scope.
