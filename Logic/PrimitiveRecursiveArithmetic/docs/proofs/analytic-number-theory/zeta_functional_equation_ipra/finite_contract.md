# Concrete finite arithmetic contract

This specification fixes one total PR checker. It is additional detail for
the final module plan, not a claim that its object derivation has already
been implemented in Lean.

## Conventions

For `n>=1`, let `lambda(n)` be the least `j<=n` such that `n<=2^j`, and put
`lambda(0)=0`. This is a **bounded** search, hence primitive recursive. It
satisfies `n<=2^lambda(n)` and is the ceiling binary logarithm.

Use the rational complex norm `norm1(x+iy)=|x|+|y|`, so norm calculations
and every final comparison are exact rational arithmetic. It is
submultiplicative; the usual modulus is at most `norm1` and `norm1` is at
most twice the usual modulus. No square-root comparison is needed in the
checker.

The primitive input is a natural code `c` for `s=x+iy` with `x,y` rational,
an integer `B>=2`, and a precision `k`. The valid domain is `|x|,|y|<=B`.
Return 1 immediately on malformed codes, on `B<2`, or outside that box.
The nontrivial branch below returns the characteristic function of one
exact rational inequality.

## Explicit finite approximation to J

Let `J(s)=integral_1^infty psi(t)t^(s/2-1) dt`, with
`psi(t)=sum_(n>=1) exp(-pi*n*n*t)`.
For a box bound `B>=2` and requested `p`, set

```
T = p + lambda(B!) + 4
N = p + (B+1)*lambda(T) + 4
D = 2*(B+2)*T^B
q = p + lambda(T*D) + 4
r = p + lambda(T) + 4
M = (T-1)*2^q
t_j = 1 + j/2^q                       (0 <= j < M)
g_N(t,s) = sum_(n=1)^N exp(-pi*n*n*t + (s/2-1)*log(t)).
```

Let `gHat_N(t,s)` approximate the entire sum in `norm1` with error at most
`2^-r`. It suffices to approximate each of its `N` summands at precision
`r+lambda(N)+1`, leaving half of the budget unused; the fixed checker
keeps the rational sum exact.
Then put

`JHat(B,p,s)=2^-q * sum_(j=0)^(M-1) gHat_N(t_j,s)`.

All values in this formula are rational complex numbers. In particular the
mesh is a rational power-of-two mesh and all loops have explicit PR bounds.

The proof gives the following four independent `norm1` errors:

```
t > T:                 2*B!*2^(-2*T)
n > N, 1 <= t <= T:    4*T^(B+1)*2^(-3*(N+1)^2)
left-rectangle mesh:   T*D*2^(-q)
point evaluation:      T*2^(-r).
```

Their sum is strictly less than `2^-p`. Here are the elementary estimates
justifying the constants:

- For `t>=1`, `pi>=3`, and `e>=2`,
  `psi(t)<=2 exp(-3t)` and `t^B<=B! exp(t)`.
  Including the conversion from complex modulus to `norm1` gives the
  first bound after integrating `4 B! exp(-2t)`.
- For `n=N+1+j`, `n^2>=(N+1)^2+j`; the geometric tail has ratio at most
  `2^-3` and hence is at most twice its initial term. Also the weight has
  `norm1` at most `2T^B` and the interval length at most `T`.
- The finite sum `psi_N` satisfies `psi_N<=1` and `|psi_N'|<=1`.
  Indeed,
  `4 n^2 2^(-3n^2) <= 2^-n`, because `n^2<=4^(n-1)` and `n^2>=n`.
  Summing the last bound gives 1. The derivative of `t^(s/2-1)` and
  `|s/2-1|<=B+1` now give `norm1(g_N')<=D`.
- A left-rectangle mesh of width `h=2^-q` on an interval of length at most
  `T` has error at most `TDh`. The finite point-evaluation error sums to
  at most `T2^-r`.

The first error is at most `2^(-p-7)`. The last two are at most
`2^(-p-4)` each. The second is much smaller than `2^(-p-4)` by the displayed
choice of `N`. This leaves ample budget for using non-strict rational
inequalities in the checker.

## One fully bounded elementary evaluation routine

The elementary approximation routines need not use a search for
convergence. For example:

1. Approximate `pi=4 atan(1)` by the alternating series with
   `2^(u+3)` terms to error less than `2^-u`.
2. For rational `1<=t<=R`, use
   `log(t)=2 sum_(j>=0) y^(2j+1)/(2j+1)`, `y=(t-1)/(t+1)`.
   Taking `R*(u+2R+4)` terms gives error less than `2^-u`:
   the tail is at most `2R^2 exp(-(2L+1)/R)`.
3. For a rational complex argument of `norm1` at most an integer `W>=1`,
   use the exponential Taylor polynomial through degree
   `m=4W+u+4`. The tail after degree `m>=2W` is at most `2^(4W-m)`:
   the degree-`2W` term is at most `exp(W)<=4^W`, and successive
   term ratios thereafter are at most `1/2`. This is the degree rule
   used in the main report and gives error smaller than `2^-u`.

For a summand in `JHat`, let

```
U = (4N^2+B+2)*T
C = N^2*T+B+1
v = u + 2U + C + 4.
```

Approximate `pi` and `log(t)` to precision `v`, form the exponent exactly
from these rational approximations, then approximate its exponential to
precision `u+1` using the Taylor rule. The exponent error is at most
`C2^-v <= 2^(-u-2U-4)`, and its true norm is at most `U`. The exponential
Lipschitz factor on the enlarged box is at most
`2 exp(U+1) <= 2^(2U+3)`. Thus the argument perturbation costs at most
`2^(-u-1)`, and the final Taylor approximation costs at most another
`2^(-u-1)`. The total summand error is at most `2^-u`.

These counts are intentionally generous. They show PR totality without
introducing an unbounded precision search. Faster implementations are
permitted only after proving that they meet the same error contract.

## Common finite xi approximation

For the original input box choose `A=B+3`, so both `s` and `1-s` lie in the
box of radius `A`. For a requested xi precision `w`, put `pJ=w+4A+8` and
define

```
xiHat(A,w,s) = 1/2 + s*(s-1)/2 *
    (JHat(A,pJ,s) + JHat(A,pJ,1-s)).
```

Because the same `A` and `pJ` are used for both arguments, this rational
finite expression satisfies

`xiHat(A,w,1-s) = xiHat(A,w,s)`

**exactly**, by the polynomial identity. It also approximates `xi(s)` to
`norm1` error at most `2^-w`, since the error is at most
`4A^2 2^-pJ`. The exact symmetry of this finite expression is useful, but
does not replace the nontrivial Mellin identification theorem.

## Reciprocal gamma evaluator

The gamma construction provides, for `|z|<=D>=1`, the explicit bound

`|R_N(z)|, |R(z)| <= M_D := D*4^(D+D^2)`

and, for `N>=J_D:=2(D+D^2)`,

`|R_N(z)-R(z)| <= C_D/N`, `C_D=2M_D(D+D^2)`,

where `R_N(z)=z N^(-z) product_(n=1)^N (1+z/n)`.
Choosing `N=max(J_D, 2^(w+4)C_D)` gives ample tail budget for `norm1`
precision `w`. The finite rational product is exact. Only the final
exponential defining `N^(-z)` requires approximation.

For an explicit, deliberately coarse schedule, let
`Q=D(N+1)^D`, `S=D(N+1)+1`, and
`v=w+2S+Q+D+14`. Approximate `log N` to error `2^-v`, and its resulting
complex exponential to the same accuracy, by the bounded routines above.
The finite product has modulus at most `Q`, and exponential perturbation
is bounded by `2exp(S)`. These margins make the total `norm1` error less
than `2^-w`. The fixed checker does not apply final dyadic rounding.
Use the common bound `D=2A` for every reciprocal-gamma factor below.
For these specific arguments it bounds both `norm1` and the usual
complex modulus, so the exponential input bound also meets the stated
Taylor-evaluation contract.

## Deterministic remaining elementary factors

For the powers and sine in the final residual, fix

`v = w + 16A + 30`.

Approximate `pi`, `log(2)`, and `log(piHat)` to precision `v`, first
clipping the rational approximation `piHat` to `[3,4]`. Use the finite
series rules above, with their bounds determined by `A` and `w`. The
error of the resulting logarithm as an approximation to `log(pi)` is
at most `2*2^-v`, since the logarithm is `1/3`-Lipschitz on `[3,4]`.

Form the required exponents rationally and evaluate each exponential
to precision `w+4`. Every exponent has `norm1` at most `4A+1`, and its
perturbation is at most `4A*2^-v`. The exponential perturbation bound
therefore makes each resulting analytic factor accurate to better than
`2^-w`. Evaluate sine as
`(exp(i*z)-exp(-i*z))/(2*i)`, using the same precision for both
exponentials. Keep the resulting rational sums and products exact.

This rule fixes the elementary-factor branch of the checker; there is
no search for an adequate precision and no unspecified choice of a
magnitude or amplification bound.

## Final finite residual

Let `A=B+3` and `H=2^(64A^2)`. Every exact analytic factor in the two
expanded sides below has `norm1` at most `H`:

```
L(s) = s * R(1-s) * pi^(s/2) * R(1+s/2) * xi(s)
RHS(s) = (1-s) * 2^s * pi^(s-1) * sin(pi*s/2)
                  * pi^((1-s)/2) * R(1+(1-s)/2) * xi(1-s).
```

For reciprocal gamma this follows from the preceding `M_D` with `D=2A`.
For `J` one has `norm1(J)<=2A!`; hence
`norm1(xi)<=1/2+8A^2 A! <=2^(8A^2)`. The powers and sine are bounded by
elementary exponential inequalities, all much smaller than `H`.

Choose the working precision

`w = k + 512A^2 + 20`.

Evaluate each analytic factor to `norm1` error at most `2^-w`, using
`xiHat`, the reciprocal-gamma evaluator, and the deterministic
elementary-factor schedule above. Keep the factors `s` and
`1-s` and all multiplications rational and exact. Call the resulting
rational values `LHat`, `RHat`.

The standard telescoping formula for the difference of products of at
most eight factors bounds the aggregate evaluation error by

`2^11 H^7 2^-w < 2^(-k-8)`.

The human proof of the entire functional equation, applied at the
allocated finite accuracies, supplies the same residual identity budget.
Equivalently, in the analytic shorthand it proves `L(s)=RHS(s)`, and the
finite error inequalities remove that shorthand. The checker returns the
truth value of

`norm1(LHat-RHat) <= 2^-k`.

This is the promised total PR relation `Check(c,B,k)`. Its correctness is
the closed iPRA sentence formed in `ArithmeticBridge.lean` from the fixed
compiled PR definition. The final formalization must actually compile
these definitions and construct the `Prf PRAAx` derivation; this
specification alone does not provide that proof term.

## Explicit reading index for a fixed PR complex name

Suppose the fixed PR name `a(n)` has the supplied regularity bound
`norm1(a(p)-a(q)) <= 2^-p+2^-q` and a numerical box bound. Use the
enlarged box `A=B+3`. Keep every cutoff and Taylor degree determined
by that common box and the requested precision, and retain exact rational
sums and products. Each finite approximant to the entire functions, as a function
of `s`, is then a rational complex polynomial

`P(s) = sum_j a_j s^j`.

The rational pi and logarithm approximants used in its construction are
constants independent of `s`. Compute by a finite coefficient fold

`K = 1 + ceil(sum_(j>=1) j*norm1(a_j)*(2A+2)^(j-1))`.

The finite difference-of-powers identity gives
`norm1(P(s)-P(t)) <= K*norm1(s-t)` on the enlarged box. At requested
precision `k`, first choose the expression's uniform approximation
accuracy as `k+4`, compute its corresponding `K`, and read the input at

`m = k + lambda(K) + 8`.

The regularity inequality and the polynomial bound absorb the input
error; the uniform analytic tail bounds absorb the finite-expression
error. This is an explicit PR rule for each fixed input definition.
It proves the schema for PR names without a universal PR evaluator or
an exact zero test. Pointwise division still requires a separate
numerical apartness witness; the everywhere-defined cleared identity
does not.
