# Independent forward and coefficient-field checks

## Warning

Every decimal amplitude below is an **uncertified floating-point, finite-n
diagnostic**.  No interval enclosure, theorem about these numerical errors,
or certified decimal value of gamma is claimed.  These computations do not
enter the analytic proof.

## Original-row forward recurrence

The script `check_forward_numerical.py` uses neither the Jacobi reduction nor
the formal profile recurrence.  It sets

v[n,k]=A[n,k]/(12^n n!)

and computes each complete row directly by

v[n,k]=sum_{r=0}^k [(2n+r-1)/(12n)] v[n-1,r],

with v[0,0]=1 and zero padding.  This also reproduces the k=0
double-factorial boundary.  A single positive NumPy cumulative sum computes
each row.  The run to n=50000 took approximately 5.5 seconds.

Put B=3^(1/3)z and define the raw finite-n amplitude

Gamma_0(n)=v[n,n] exp(-B n^(1/3)) n^(2/3).

The successive corrected values are

Gamma_r(n)=Gamma_0(n) exp(-sum_{k=1}^r L_k n^(-k/3)),

where L_1=B^2/18, L_2=0, L_3=-1/9, L_4=-B^2/162.
Orders 1 and 2 therefore agree exactly.

| n | Raw amplitude | After order 1 or 2 | After order 3 | After order 4 |
|---:|---:|---:|---:|---:|
| 1000 | 2.154286725924319 | 2.022401865108398 | 2.022626588911168 | 2.022640786414359 |
| 3000 | 2.113125481149931 | 2.022563630558822 | 2.022638541710152 | 2.022641823053657 |
| 10000 | 2.082805604064423 | 2.022618857429427 | 2.022641331097140 | 2.022641990089460 |
| 20000 | 2.070256135659065 | 2.022630509183142 | 2.022641746050518 | 2.022642007571821 |
| 30000 | 2.064177881815730 | 2.022634367935080 | 2.022641859187353 | 2.022642011493958 |
| 50000 | 2.057620753828378 | 2.022637441981277 | 2.022641936736142 | 2.022642013812363 |

These successive corrections show the expected improved convergence.
The final entry is still a finite-n approximation, not a reported value of
the limit.  No extrapolation or fitted coefficient was used.

Small-n validation independently computes unbounded integer A[n,k] through
n=80.  The diagonal starts 1,7,106,2575,87595 (after a_0=1), and the maximum
relative difference from the floating normalized rows is 6.7e-16.  A second
run using NumPy longdouble through n=10000 gives the fourth-corrected value
2.0226419900895007; its relative difference from float64 is 2.0e-14.  The
Airy zero used by both is supplied in double precision by SciPy, so this
cross-check does not independently bound the common Airy-zero error.

Reproduce with:

python check_forward_numerical.py --nmax 50000 --extended-check 10000

Complete checkpoint values, timings, and warnings are in
`forward-numerical.json`; the console transcript is `forward-numerical.out`.

## Natural Q[B] coefficient field

The coordinate change in the main proof §7 is correct.  Set

t=(N/2)^(-1/3), y=(j+1)t, B=3^(1/3)z.

Then epsilon=2^(-1/3)t, x=2^(-1/3)y,
ell=(2^(2/3)/3)B.  The original coefficient and previous-time dilation become

a=1-y t^2/[3(1+y t^2/2-t^3/2)],
t_previous=t(1-t^3/2)^(-1/3),
y_previous,plus/minus=(y plus/minus t)(1-t^3/2)^(-1/3).

The Airy equation is Ftilde''=(y+B)Ftilde/3.  Its polynomial elimination
operator is

TQ=-Q'''/2+(2/3)(y+B)Q'+Q/3.

On y^d the leading coefficient is (2d+1)/3, a nonzero rational number.
Consequently the all-orders inverse on polynomials requires divisions only
by rational numbers.  The boundary scalar and derivative gauge preserve
Q[B]; the scalar antidifference has new diagonal coefficient -r/6, again
nonzero and rational.  The normalized endpoint Taylor recursion, logarithm,
and exponential likewise use only rational operations.  Thus every
normalized endpoint/logarithmic/multiplicative coefficient belongs to Q[B]
as claimed.  The overall amplitude gamma is not included in that statement.

`check_natural_field.py` separately reconstructs this natural-coordinate
operator instead of merely substituting into the old results.  It verifies
the exact residual through t^7, checks every polynomial with SymPy domain
QQ[B,y], and independently matches the rescaled epsilon coefficients.
Its scalar coefficients in 2(1+sum s_m^(t)t^m) are

s_2^(t)=B/6,
s_3^(t)=-1/6,
s_4^(t)=B^2/216,
s_5^(t)=B/54,
s_6^(t)=-(B^3+72)/1296,
s_7^(t)=49B^2/6480.

It derives, without using them as input, the diagonal logarithmic corrections

[B^2/18, 0, -1/9, -B^2/162].

The endpoint divided by Ftilde'(0)t is

1+(B/18)t^2-t^3/6+(B^2/1080)t^4+O(t^5).

Reproduce with `python check_natural_field.py`.  Complete expressions and
checks are in `natural-field.json`, with transcript `natural-field.out`.

## Spectral and endpoint notation check

The separate exact-tridiagonal numerical check is already in
`check_frozen_numerical.py` and `frozen-numerical.json`.

For avoidance of ambiguity, the normalized frozen endpoint expansion is

psi_N(0)=sqrt(2/3)N^(-1/2)
         [1+ell N^(-2/3)+(1/3)N^(-1)+O(N^(-4/3))].

The third displayed correction is **(1/3) times N^(-1)**.
