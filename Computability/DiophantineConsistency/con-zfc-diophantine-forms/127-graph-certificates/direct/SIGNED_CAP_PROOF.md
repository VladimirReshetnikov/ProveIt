# Simultaneous index and sign recovery from one bounded Pell congruence

## 1. The explicit integer equations

The principal fixed polynomial is the sum of squares of the 225 complete
quadratic residuals in `integer381/equation.json`. Its 381 variables range
over all integers. Its exact degree is four; its complete collected
coefficient map has 13,179 monomials and height 2,445,790,974,704.
The lower-height companion in `integer391` has 391 unrestricted integer
variables, 235 residuals, 10,764 monomials and height 80,496,640.

Both are ordinary Diophantine equations: the auxiliary sign witnesses are
among the declared integer coordinates, every coefficient is fixed, and no
inequality or special arithmetic predicate is implicit in the final equation.
The inherited C222-to-ZFC refutation calibration and the ordinary proof
below give, within ZFC, unsolvability if and only if Con(ZFC). Neither
consistency nor inconsistency is assumed. No new end-to-end proof-assistant
derivation, object-language ZFC proof term, global optimum or worldwide
priority is asserted.

The latest inspected incoming direct integer quartic has 442 variables,
290 rows, 4,652 terms and height 128,446. The 381 form saves 61 variables
and 65 rows, with more terms and larger coefficients. The 391 form saves
51 variables and 55 rows and gives the useful lower-height tradeoff.
There is no claim to dominate that predecessor in every metric.

## 2. A signed Pell cap theorem

For A>=2 write `(X_j(A),Y_j(A))` for the canonical Pell sequence of
`X^2-(A^2-1)Y^2=1`. Suppose:

* W>=4 and A-1>4W^3;
* k_1,...,k_m are positive integers with k_i<W and m<=W-2;
* V=Y_W(A) is already certified;
* x_i,y_i,Q are arbitrary integers, while s>=0;
* the principal norm and the two global rows hold:

      x_i^2-(A^2-1)y_i^2=1,                         (2.1)
      V=W+1+s+sum_i y_i^2,                         (2.2)
      sum_i[(y_i-k_i)^2+(x_i-1)^2]=(A-1)Q.         (2.3)

Then every pair is exactly the positively oriented canonical pair
`(x_i,y_i)=(X_(k_i)(A),Y_(k_i)(A))`. No individual sign or index-range
guard is needed for x_i or y_i, and no sign assumption on Q is needed.

### Proof of soundness

Signed Pell classification gives independent signs epsilon_i,delta_i in
{1,-1} and a unique j_i>=0 with

    x_i=epsilon_i X_(j_i)(A),
    y_i=delta_i Y_(j_i)(A).

For j_i=0 the ordinate sign is immaterial. By (2.2), y_i^2<V. Since
|u|<=u^2 for every nonzero integer u, and also 0<V, this implies
|y_i|<V=Y_W(A). Strict monotonicity gives j_i<W.

The recurrences modulo A-1 give `X_j(A)=1` and `Y_j(A)=j` in that
modulus. Therefore (2.3) implies that A-1 divides the nonnegative integer

    E=sum_i[(delta_i j_i-k_i)^2+(epsilon_i-1)^2].

Here |delta_i j_i-k_i|<=2(W-1) and (epsilon_i-1)^2<=4. Hence

    0<=E<=m[4(W-1)^2+4]<4W^3<A-1.

It follows that E=0. Each epsilon_i=1, and delta_i j_i=k_i>0 forces
delta_i=1 and j_i=k_i. This proves all indices and all thirty principal
coordinate signs simultaneously. In particular it excludes the negative
abscissa even in the degenerate ordinate-zero case. The conclusion uses
the sum of both types of square error; omitting the x_i-1 errors would
leave the abscissa signs uncontrolled.

### Constructive completeness

For the source application strengthen the hypothesis to `2k_i<=W-1`
and A>W+1. Choose all principal pairs canonical. Every y_i-k_i and x_i-1
is divisible by A-1, so (2.3) defines a nonnegative integer Q.

The addition formula gives `Y_(2k)(A)=2X_k(A)Y_k(A)>Y_k(A)^2` for k>=1.
Consequently

    sum_i Y_(k_i)(A)^2 < m Y_(W-1)(A).

Also `Y_W(A)>(2A-1)Y_(W-1)(A)`. Since m<=W-2 and A>W+1, the difference
between Y_W(A) and the sum of squares exceeds W+1. Thus (2.2) supplies
the natural integer `s=Y_W(A)-W-1-sum_iY_(k_i)(A)^2`.

These are explicit witnesses. The theorem does not rely on finding a
small sample of compatible indices or on an assumed noncancellation of
the large Pell ordinates.

## 3. The square frame supplies every hypothesis

Use exactly the same 23 semantic atoms Acal as in the natural construction,
including all fifteen positive numerator or power indices. Replace its
frame by

    W=2+sum_(a in Acal) a^2.                         (3.1)

All semantic power outputs may initially be signed. Nevertheless every
integer atom has absolute value less than W. The fifteen index expressions
are positive before interpreting any power: they are the padded horizon,
the positive amplification, x+1,y+1, F^2+t, the nine shifted encoded
representatives and the positive derived-label expression, with duplicates
identified as in the literal graph. Their positivity uses only the guarded
presemantic source witnesses and positive defining gates. The checker
traces those dependencies and never assigns a nonnegative lower bound to
an unproved power output.

Because the fifteen distinct index atoms are positive, (3.1) gives
`m<=W-2`. For each index, `W>=k_i^2+2>=2k_i+1`, so `2k_i<=W-1`.
The zero-index version of a general square-frame theorem would require
an additional count bound; no zero index occurs in this source. The
literal t>=16 also gives W>=258, well above the theorem's W>=4 threshold.

The scale equation is unchanged:

    L^2-((W+1)^2-1)(WZ)^2=1,
    A=L+sigma,

with L,sigma>=0 and Z>=1 supplied by explicit guards. As in the natural
proof, A>=(W+1)^W. For W>=4,

    A-1 >= (W+1)^W-1 >= (W+1)^4-1 >4W^3.

The single cap's full indexed-Pell criterion still has natural witnesses.
Its missing index-margin condition W<=V follows from (2.2). The finite
sign certificate proves the natural signs of every witness needed for
that cap before the new signed theorem is invoked.

Thus (3.1), (2.2) and (2.3) are the only three changed raw polynomial
rows. Every principal-pair norm and every other source row is unchanged.
All three are quadratic after the existing gate cuts.

## 4. Power signs can be recovered in order

The new theorem first identifies every principal pair exactly. For an
exact request the retained equality is

    X_k(A)+(n-A)Y_k(A)=m+T_n u,
    T_n=2An-n^2-1.

The quotient u, the output m, and the modulus-coordinate T_n need no
separate sign constraints. Suppose n is already positive. From the square
frame, `1<=n,k<W` and `|m|<W`. Since A>=(W+1)^W and W>=4, the polynomial
`2An-n^2-1` is increasing for 1<=n<W and

    T_n>=2A-2>W^W+W.

Also `0<n^k<= (W-1)^(W-1)<W^W`. The standard Pell congruence says
`T_n divides m-n^k`. But

    |m-n^k|<W+W^W<T_n,

so m=n^k>0. The modulus coordinate is positive automatically. Once m is
the true least positive residue, positivity of the Pell expression gives
u>=0 as well, though its sign was not needed for soundness.

The exact six calls are ordered. Their first bases are `F^2+1>=1` and
`B=b0+2>=2`, independent of power semantics. Recovery of `N=B^K` supplies
the positive base for `q=N^K`, and recovery of q supplies the bases for
the three q-powers. All exponents were already positive in Section 3.
Thus this reasoning is sequential, with no use of an output sign before
its own power is established.

The integer inference algorithm's original 61 guards included two power
output guards, four modulus guards and three divisibility-quotient guards.
The argument here removes those nine actual guard graphs. Other power
output signs already followed from digit remainder rows and cost no guard.
The final equation has 52 explicit nonnegativity graphs.

## 5. Modular and CRT quotient signs are unnecessary premises

The common-root equation is used only as an integer congruence when
proving the modular Pell residue identity. Its quotient need not be
nonnegative. At a correctly decoded zero, q>0 and the large frame makes
A>q+1, so its actual quotient is nonnegative anyway. Constructive
completeness may simply choose a sufficiently large member of the soluble
A residue class, exactly as in the natural proof.

The eleven modular-digit quotients are used only through integer
congruences. The low remainder and its complement retain their explicit
nonnegative guards. Once the canonical pair and positive q,N are known,
the modular Pell expression is positive and the selected low residue is
the least nonnegative residue modulo the relevant positive modulus.
The actual quotient is consequently nonnegative.

The CRT index row uses an arbitrary integer quotient of the positive
quantity `C+F^2+1` by the ultimately positive B. Its sign follows after
these values are interpreted. The local evaluation row likewise uses an
integer quotient of a nonnegative source polynomial by positive N.
Neither sign is a premise of the Horn/CRT decoding argument. Completeness
chooses the same nonnegative quotients supplied by the inherited source.

## 6. All remaining signs are literal polynomial constraints

For every one of the 52 selected semantic coordinates z, append a private
triple of integer variables a,b,c and the quadratic row

    z=a^2+b^2+c(c+1).                                (6.1)

The right side is nonnegative for all integers. Conversely it represents
every natural z: Legendre's three-square theorem applies to 4z+1, which
is never of the forbidden form `4^r(8s+7)`. In a representation as three
squares exactly one summand is odd modulo four. Writing that one as
(2c+1)^2 and the others as (2a)^2,(2b)^2 yields (6.1).

Every additional required semantic nonnegativity follows from an explicit
finite certificate of 174 row consequences. A typical step is a positive
integer multiple of z equal to a sum of monomials with known nonnegative
odd factors; another allowed step is equality to an exact affine square.
All dependencies are already known when a step is applied. This includes
the complete single indexed cap before its interpretation.

The 61 semantic coordinates excluded from the set whose signs are required
from this elementary closure are exactly the thirty principal Pell
coordinates, the power and modular quotients, the one pooled-error
quotient, the six power outputs, the four modulus coordinates, and the
three later divisibility quotients. Some of their signs are incidentally
obtained by the closure; those facts are not premises of the semantic
recovery. Their roles and soundness are proved in Sections 2-5; they are
not silently treated as natural. Every ordinary arithmetic gate has its literal
defining equation. Signs of any such gates that are needed later follow
once their source inputs have been recovered.

## 7. The complete refutation equivalence

Given an integer zero, the guard and row certificates establish all
presemantic source signs and the one natural indexed cap. The square
frame bounds all signed semantic atoms. The new oriented-cap theorem
then recovers all principal pairs. The sequential signed-power argument
recovers all six exact powers. The common modular-root congruence gives
the one exact binomial and ten range digits. The independent radix
bootstrap, factorial fixed point, prime-power CRT and Horn-flow argument
are exactly the inherited natural proof. Thus one obtains a finite C222
refutation and hence a finite ZFC refutation.

Conversely a finite C222 refutation supplies the same bounded source,
factorial, beta parameters, CRT representatives and semantic powers as
before. Compute the square frame W from those data. The cofinal common
root permits a sufficiently large A. Section 2 supplies the squared
cap slack and oriented-error quotient; the inherited indexed cap and
canonical principal pairs supply every norm witness. All remaining
quotients can be chosen as in the natural proof. Legendre's theorem
supplies the 52 private guard triples. Thus every quadratic residual is
zero. This proves existence equivalence in both directions.

The named inherited logical endpoints are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The construction
uses the numerical proof calculus, not a Turing-machine run and not a
universal-polynomial specialization. Its ordinary finite arithmetic and
number-theoretic proof is formalizable in ZFC; the new mathematical
and finite-verification scopes are kept separate.

## 8. Exact compilation and independent verification

The three changed rows act on the previous 349-coordinate raw quadratic
graph. The 52 guards add 156 coordinates and 52 rows, giving 505 integer
coordinates and 349 quadratic residuals. Exact integral monic
substitution removes 124 coordinates and rows to give the principal
381-variable, 225-row form. No unconstrained coordinate is removed.
Restricting the support of affine substitutions gives the 391-variable
companion and its smaller coefficient height.

`check_signed_cap.py` imports no producer, sign-inference algorithm or
coordinate optimizer. It independently derives all three changed rows
from the actual semantic atoms, compares every unchanged row, proves
each required sign step, checks every private guard graph, verifies all
fifteen positive indices before powers, checks the ordered positive-base
schedule, replays every signed restoration, and compares every coefficient
of the fully collected quartic. Changed source coefficients, guard
coefficients, sign proofs, restoration coefficients and final polynomial
coefficients are rejected by separate negative controls. Normal and
optimized Python enforce the same checks with explicit exceptions.

The complete proof remains the ordinary argument above plus its retained
source calibration. The finite checks do not search for a refutation or
infer consistency from the absence of small roots.
