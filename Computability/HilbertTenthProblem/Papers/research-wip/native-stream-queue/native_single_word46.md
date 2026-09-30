# A complete native positive-word predicate in 45 operations

The exact native-word predicate below costs **45=25M+20A**, with 12
equations and 18 positive auxiliaries. Its necessary parity follows from
the generic signed Pell theorem. We first give the independently reviewed
46-operation version with explicit parity, then prove the saving.

One bounded ternary word can use the retained 43-operation Pell core
directly, with its word also serving as the packed index and its length
power serving as the scale. Three additional operations pay the word
bound, an even-index condition and the small-index exclusion needed by
the proof. The result is **46=26M+20A**, with 12 equations and 18 strictly
positive auxiliaries beyond two positive parameters.

This is a complete typing relation. It does not include a program-specific
mask, synchronized controller, ordinary-input initialization, routing or
acceptance. The established complete universal bound remains 76.

## Source and exact projection

Take positive parameters q,r. Supply the sixteen Pell coordinates other
than r from the [retained ternary core](native_controller_three_selector_53.md),
and two more positive coordinates nu,alpha. Set the core scale to D0=q:
the registers X=wq and Y=sq still each cost their usual multiplication.
Add

    r=2nu+12,              r+alpha=q.                    (1)

The three literal instructions are `twice_nu=2*nu`,
`index_lower=twice_nu+12`, and `word_bound=r+alpha`; their two comparisons
are free. There is no repunit register or free conversion in this source.
The original seventeen-coordinate core included r; making r a parameter
leaves sixteen quantified core coordinates, hence eighteen auxiliaries
after (1). The 45-operation refinement below retains this reviewed source
as a reference and proves that its paid parity multiplication is redundant.

For mathematical notation put

    X=wq, Y=sq, E=XY, A=a+3, Delta=A^2-1,
    M=6a+8, J=2r+1, R=ic^2, u=J+jc.

The ten unchanged core equations are

    tau(tau+1)=((XY)^2+X)(Yk)^2,
    c=Yk+eta, k=eta+zeta, k=r+1+hXY,
    a=Y(X+1), d=X+ac+gaM,
    d^2=1+Delta*c^2,
    R^2=Delta*(f^2-1),
    R^2*(u^2-y_aux^2)=1-y_aux^2,
    u=c+of.                                               (2)

Every displayed multiplication and square is evaluated by the imported
43-instruction core. Only its scale operand is renamed from `n2` to the
already supplied q. The independent polynomial audit retains the usual
auxiliary-norm residual correction.

**Exact theorem.** Equations (1)--(2) have positive witnesses if and only if

    q=3^t for some t>=3,
    r has exactly t ternary digits, each in {1,2},
    its units digit is 2, and r is even.                  (3)

Evenness is explicitly paid in (1). The argument does not infer a parity
necessity from a kernel whose previously proved converse assumed parity.

## Bootstrap before power or digit recovery

Positivity in (1) gives r>=14 and q>=r+1>=15. Consequently

    X,Y>=q, XY>=q^2>r+1,
    a>=q(q+1)>2r+1,
    6r/a<6/(q+1)<=6/16<1/2.                            (4)

No power hypothesis, digit bound on r, or condition q<r^2 has been used.
The latter is needed only to simplify the eventual converse.

The first Pell norm has base B=2XY^2+1 and positive index n. Its
congruence modulo XY, together with k=r+1+hXY and XY>r+1, gives
n=r+1+vXY for v>=0. The main Pell norm has c=psi_A(p). Since B>A
and c>Yk>k, its index p>=n+1>=r+2>=16. Thus

    c>A^6>A*Delta^2, c>Y(r+1)>J, 0<2p<=c.

These are the exact hypotheses of the retained auxiliary-rank and
half-parameter arguments. They recover p=J. The difference

    (2B-1)-4A=4Y(X(Y-1)-1)-11>0

then excludes v>=1 by the retained growth estimate, giving n=r+1.
These arguments use the core equations at the actual scale q, not a
larger inherited lower bound on a previous packing scale.

Write xi=(X+1)^(2r)/X^r. The core Pell estimates and (4) give

    xi<c/k<xi*(1+12r/a),
    Y>=X^r, a>X^(r+1), 0<c/k-xi<24r/(X+1).

The exact recurrence for chi_A(j)-a*psi_A(j) modulo M gives
X=3^J modulo M. Both sides lie strictly between zero and M: X<a,
and X>=15 implies

    3^J=3*9^r<X^(r+1)<a<M.

Hence X=3^(2r+1) as an integer. Since q divides X and q>=15, unique
factorization gives q=3^t with t>=3. Now X>48r; the ratio error is
below 1/2 and the binomial tail is below 1/6. The unit interval forces

    Y=floor((X+1)^(2r)/X^r),      q divides binom(2r,r).  (5)

All generic estimates cited here are the explicit inequalities in the
[base-three kernel proof](../../1980/EXPLORATION_BASE_THREE_PELL_KERNEL.md),
Sections 2--6. Their required numerical hypotheses were rechecked in
(4) and the subsequent index argument.

## Native digits and the complete positive converse

The paid bound is 0<r<q=3^t. Doubling r has at most t outgoing ternary
carries. Kummer's formula and (5) require at least t, so all positions
must produce a carry. The first trit must be 2; with that incoming carry,
each higher trit must be 1 or 2. Equation (1) also makes r even. This
proves (3) without a field-carry or packed-overflow assumption.

Conversely suppose (3). The least native word with units 2 is
(q+1)/2, so

    r>=(q+1)/2>=14,       q<=2r-1<r^2.

Take nu=(r-12)/2 and alpha=q-r, both positive integers. Every doubling
position carries, so (5)'s divisibility holds. The canonical core map is

    J=2r+1, X=3^J, w=X/q,
    Y=floor((X+1)^(2r)/X^r), s=Y/q,
    a=Y(X+1), A=a+3, Delta=A^2-1, B=2XY^2+1,
    c=psi_A(J), d=chi_A(J), k=psi_B(r+1),
    eta=c-Yk, zeta=k-eta, tau=(chi_B(r+1)-1)/2,
    h=(k-r-1)/(XY), ga=(d-X-ac)/(6a+8),
    m=2cJ, f=chi_A(m), i=Delta*psi_A(m)/c^2,
    R=ic^2, y_aux=psi_R(J), u=chi_R(J)/R,
    o=(u-c)/f, j=(u-J)/c.

Since q<r^2<X and q,X are powers of three, w is a positive integer;
the central-binomial divisibility gives the same for s. The exact ratio
and tail estimates make eta,zeta positive. Pell congruences and growth
give positive integral tau,h,ga. The standard expansion at m proves
c^2 divides psi_A(m). Even r gives J=1 modulo 4, so the two retained
odd-index congruences yield u=c modulo f and u=J modulo c. The retained
growth bound u>c>J makes o,j positive. Every equation (2) follows.

This is the full parametric positive-witness map at the new scale, not
a claim that its enormous final auxiliary coordinates were computed.

## Boolean interpretation, cost and evidence limits

Mathematically define H=(q-1)/2 and D=r-H. Then D is a Boolean ternary
word, its units digit is 1, and its number of ones has the same parity
as t. H and D are decoded values in this statement; producing them as
arithmetic registers is not part of 46. If a containing source needs H,
supplying it with q=H+H+1 costs two additions; computing D=r-H costs
one further subtraction. These costs must be included in any composition.

The [checker](native_single_word46.py) independently expands all twelve
source residuals, including the auxiliary correction, and audits the
46-instruction schedule. It tests preliminary bounds at nonpower q as
well as powers, and compares factorial valuations against the exact word
predicate through ternary length ten. Two actual admitted q=27 values,
r=14 and26, check the changed scale divisibilities and exact main/first
Pell estimates. The auxiliary extension is provided by the proof.

Run the checker without arguments to compare the
[receipt](native_single_word46.json). Independent full proof/source/default
review of the 46-operation source passes, including its use of the relaxed
rank and half-parameter lemmas. The refinement below has separate review.

## 45 operations using necessary signed parity

Replace only the first equation of (1) by

    r=nu+13.                                             (6)

Its single addition replaces a multiplication and an addition. The total
is **45=25M+20A**, with the same 12 equations, 18 positive auxiliaries and
two parameters. The exact projection is still (3).

Before invoking any parity statement, (6) and the word bound give exactly
the old estimates r>=14 and q>=15. Every bootstrap, index and power
argument above is parity-independent, so it recovers p=J=2r+1 and
c=psi_A(p). The relaxed auxiliary conclusion supplies

    f=chi_A(m), c divides m, m>=c>2p, f>2c,
    R=ic^2>1, c divides R, R^2=(A^2-1)(f^2-1).

Here c>2p follows already from p>=16, A>=2 and Pell growth. The source
u=J+jc=c+of is positive and gives u=p modulo c and u=c modulo f.
Thus every hypothesis of the generic signed theorem in
[the necessary parity proof, Section4](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)
holds with sigma=+1. That theorem includes noncanonical auxiliary indices
and both step-down signs; it gives p=1 modulo4, hence r even. Applying it
here does not import an even-index converse into a soundness argument.

This supplies precisely the evenness formerly paid in (1). The converse
uses the same full positive Pell map and replaces only nu by r-13>0.
It satisfies (6), proving both directions of the 45-operation theorem.
If H and D are needed as arithmetic registers, their same three additions
or subtractions make the resulting interface cost 48.

The checker expands the 45-operation source independently as well as the
46-operation reference. The pre-power enumeration now includes both index
parities; it does not assume the signed-parity conclusion when checking
the bounds. Its finite word predicate includes evenness because that
condition has a mathematical proof from the full kernel. Independent
proof/source/default review of this refinement also passes, including
the signed theorem's hypotheses before digit decoding. No new universal
bound is claimed.
