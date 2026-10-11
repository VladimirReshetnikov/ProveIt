# Independent review of parent formulas

## Cubic coincident kernel

Let `g_lambda = zeta(1-lambda,x)+1/lambda = x^(lambda-1)+h_lambda(x)`.
In a product of three factors, singleton subsets yield resonant local terms
`h_j(0) h_k(0) x^(lambda_i-1)`, while pair subsets yield
`h'_k(0) x^(lambda_i+lambda_j-1)`. The fully singular triple has
integral denominator `lambda_1+lambda_2+lambda_3-2`, nonzero near the
origin. Therefore the stated subtraction from the meromorphic integral
removes precisely all germ poles and has coefficientwise ambient finite
parts as Taylor coefficients. The correction requires full numerators,
which here happen to be independent of the subset's spectral variables.

On the diagonal, Fourier orthogonality has three choices for the lone
negative frequency and three conjugate cones. Their phases are
`exp(+-i*pi*t/2)`, yielding `6 cos(pi*t/2) T(t,t,t)` with the
Gamma and 2*pi normalization stated by parent. The three two-factor
terms give `6 A(t)^2 zeta(2t)/t^3`. Hence the diagonal formula is correct.

Expanding it independently yields
`T(0)=1/3`, `T'(0)=log(2*pi)`,
`T''(0)=log(2*pi)^2-4*zeta''(0)`.
Its constant term for `gamma_0^3` is

`T'''(0)+8*zeta'''(0)+12*(gamma+L)*zeta''(0)+L^3+6*gamma*L^2-5*gamma^3-6*gamma*gamma_1+(3/2)*gamma*zeta(2)-(3/2)*(zeta(2)+zeta'(2))`.

The negative is the `psi^3` formula implemented in parent's check.

## Distribution contact formula

With raising parameters, `G(u)` is the canonical generating distribution
for `zeta(1+u,x)-1/u`, and
`F_p(u)=D^p G(u)+H_p(u) delta^(p)`.
For correlation orientation `C(U,V)(a)=int U(x)V(x+a)dx`, expansion gives

`C(F_p(u),F_q(v))=(-1)^p D^(p+q)[Rbase + H_p(u)G(v)+H_q(v)RG(u)+H_p(u)H_q(v)delta]`.

Writing `A=A(u,v)`, `A_sw=A(v,u)`, parent Rbase simplifies to

`B Delta-A G(w)/u+G(v)/u-A_sw RG(w)/v+RG(u)/v`.

Off the identified endpoint, `Delta=-1`, so the ordinary-function
expression includes `-B`. Its canonical two-endpoint finite part differs
from Rbase by **B delta**, not B Delta. For any order r,

`D^r G(s)-FP(ordinary r-th derivative)=-H_r(s)delta^r`.

The reflected version has the same contact sign: reflection contributes
`(-1)^r` both to the ordinary derivative and to `R(delta^r)`. Thus the
base contact coefficient is

`B+(A/u+A_sw/v)H_r(w)-H_r(v)/u-H_r(u)/v`

which equals

`P_r(w)B+[H_r(w)-H_r(v)]/u+[H_r(w)-H_r(u)]/v`.

The two cross terms contribute `-H_p(u)H_r(v)-H_q(v)H_r(u)`, and the
Dirac-Dirac term contributes `+H_p(u)H_q(v)`. The overall orientation
factor is `(-1)^p`. This is exactly parent's E_pq.

Low-order independent checks: `E_00(0,0)=2*zeta(2)`,
`E_10(0,0)=1-2*zeta(2)`, `E_01(0,0)=2*zeta(2)-1`.
Swapping the factors changes the contact coefficient by `(-1)^(p+q)`,
as required by reflected correlation. The canonical two-endpoint
prescription is essential to this statement.
