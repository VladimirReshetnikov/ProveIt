# Review of the canonical counterexample height and discrepancy report

Report34, `Counterexample_Height_Expansions_and_Rotation_Discrepancy_Package.zip`,
passes this scoped analytic and source-interface review. It studies one
fixed-parameter canonical subfamily of the signed19 negative-index zeros
[already reviewed here](review_incoming_negative_index_fibers.md). Its maximum
supplied coordinate is eventually the auxiliary Pell ordinate y. Counting this
subfamily has an unavoidable rotation-discrepancy term. The report neither
classifies the whole signed19 fiber nor improves a universal arithmetic bound.

There is an additional useful exclusion: the same negative family transfers
to all eight matching signed19 children obtained from the two scales and four
protected auxiliary orientations. These are mathematically defined eliminated
systems; no new complete child gate ledgers are assigned to them. The sound
retained-positive-index parents and the 85/86-operation constructions remain
unaffected.

The [independent helper](review_incoming_counterexample_heights.py) and
[receipt](review_incoming_counterexample_heights.json) pin the archive, seven
members and four current source/proof files. They read all archives as data
and execute no archived or historical Python. Finite algebra checks support
the analysis; they are not proofs of asymptotic or Diophantine approximation
theorems. The analytic review reads `PROOF-PACKET.md`, the all-orders supplement,
the rotation audit and the transfer proof, together with the report's scope
and applicability appendix. It does not rebuild or certify the PDF.

## Fixed family and height

Fix the ordinary input, actual compiler numerals, repunit, and one prime-scale
choice from Report33. Write

    Delta=A²−1, lambda=A+sqrt(Delta), alpha=log(lambda),
    Dp=P²−1, nu=P+sqrt(Dp), beta=log(nu),
    c=psi_A(p), m=pc, Q=Delta*psi_A(m), S=p+2m,
    y=psi_Q(S).

All parameters other than the progression index p are fixed. The name alpha
here denotes a logarithm, not the supplied compiler port of that name. The
main index runs through one CRT progression p=p_b+Vr, and the first index
satisfies n=n0 mod L and Y<c/(2psi_P(n))<Y+1. The construction supplies
nineteen positive coordinates while its omitted index is R=−p.

The canonical choice m=pc is valid in the ordinary system; it need not be
its least possible auxiliary index. The report correctly counts only this
choice and S=p+2m. The inherited existence, positivity and distinct-quadratic-
field assertions are those of the full Report33 family, not new numerical
fixtures in this review.

Put d=sqrt(Delta), ell=log(Delta)/2 and epsilon=exp(−alpha p). Binet's formula
and the auxiliary hyperbolic expression give

    m=p(epsilon^−1−epsilon)/(2d),
    log y=(2m+p−1)(alpha*m+ell)+O((m+p)exp(−2alpha*m)).

Thus

    loglog y=2alpha*p+2log p+log(alpha/(2Delta))
      +d[1+(log(Delta)/alpha−1)/p]exp(−alpha p)
      +O(exp(−2alpha p)).

The coefficient and the exponential correction are consistent. In particular
log y is asymptotic to alpha*p²*exp(2alpha p)/(2Delta).

For the height claim the auxiliary norm gives U<y, hence j=(U−p)/c<y;
f<Q<y and i=Q/c²<y eventually. Also o=(U+c)/f<y for sufficiently large p.
The remaining varying supplied coordinates grow at most on the c scale or
linearly in p; the others are fixed. This accounts for all nineteen ports.
The monotonicity argument is valid: sinh(Sb)/sinh(b) increases with S>1 and
b>0 because z*coth(z) is increasing. Hence the eventual y-heights have no ties.

## All-orders expansion and its limitation

The exact algebraic normal form is

    F=(2m+p−1)(alpha*m+ell)
     =alpha*p²/(2Delta)*epsilon^−2
       *(1+A_p*epsilon−epsilon²)*(1+B_p*epsilon−epsilon²),
    A_p=d(1−1/p), B_p=d*log(Delta)/(alpha*p).

The helper proves this whole Laurent-polynomial identity with independent
formal d, alpha, p, ell and epsilon. It independently differentiates and
integrates the two formal logarithms through order24, comparing all48
coefficient polynomials with the report's power-sum recurrence. The first
two combined coefficients are A_p+B_p and −2−(A_p²+B_p²)/2.

The infinite-domain step is analytic. A_p and B_p stay bounded; the two roots
of each quadratic therefore give a uniform positive convergence radius in
epsilon. The discarded contribution to loglog y is
O(exp(−2alpha*m)/m), smaller than every fixed power of exp(−alpha p).
Consequently the convergent series sums the normal form, not the exact
height. The report explicitly preserves this distinction.

For t=alpha^−1 W(sqrt(2alpha*Delta*log B)), the leading cutoff identity is
2alpha*t+2log t+log(alpha/(2Delta))=loglog B. The inverse correction starts at

    p_B−t=−d[1+(log(Delta)/alpha−1)/t]
              *exp(−alpha*t)/(2alpha+2/t)+O(exp(−2alpha*t)).

Introducing z=1/t makes the normal-form inverse equation analytic near
(u,z,w)=(0,0,0), with nonzero u-derivative2alpha. The analytic implicit-function
theorem justifies a uniform convergent inverse series. The mean-value bound
then transfers each finite truncation to the exact cutoff while retaining
its beyond-all-orders difference. Neither inversion is permission to replace
an exact floor cutoff by a smooth value at every jump.

## Exact selection and the discrepancy obstruction

The strict first-index window is exactly

    asinh(c*sqrt(Dp)/(2(Y+1))) < n*beta
      < asinh(c*sqrt(Dp)/(2Y)).

Its length is less than delta=log(1+1/Y)<L*beta, so at most one allowed n
occurs for each p. Binet's formula places its endpoints within
O(exp(−2alpha p)) of a fixed logarithmic window. With

    theta=V*alpha/(L*beta), d_rot=delta/(L*beta),
    xi=(alpha*p_b+log(sqrt(Dp)/(2sqrt(Delta)))−log Y−n0*beta)/(L*beta),

the limiting selection is {xi+r*theta} in (0,d_rot). Irrationality and
shrinking endpoint neighborhoods already give density d_rot.

The stronger eventual exact agreement requires more. A boundary form is
p log(lambda)−n log(nu)+log(sqrt(Dp)/(2q*sqrt(Delta))), q=Y or Y+1.
It is nonzero: the automorphism reversing sqrt(Delta) and fixing sqrt(Dp)
would turn an alleged positive exponential equality into a negative one.
For fixed algebraic numbers, the effective lower bound is polynomial in p,
which eventually exceeds the exponentially small endpoint displacement.
The fixed-number estimate used here is explicitly stated in
[Bugeaud, Theorem1.1, equation(1.2)](https://arxiv.org/pdf/2209.00275).
The source statement was checked separately; this review does not reprove it.

After a finite initial cutoff, write

    D(R)=sum_{r<R} 1_(0,d_rot)({xi+r*theta})−d_rot*R,
    R(B)=max(0,1+floor((p_B−p_b)/V)).

The exact count is N(B)=d_rot*R(B)+D(R(B)). With
kappa=d_rot/(2alpha*V) and T=loglog B, this yields

    N(B)=kappa*T−2kappa*log T+D(R(B))+O(1).

If d_rot belonged to Z+theta*Z, exponentiating the relation would express
the rational number (Y+1)/Y>1 as a product of powers of algebraic units.
A rational algebraic unit is ±1, so this is impossible. The fixed-orbit
bounded-remainder criterion therefore makes D unbounded; its precise form
is [Kelly–Sadun, Theorem1](https://arxiv.org/pdf/1404.0455), checked separately.
Since R(B) traverses all sufficiently large integers, the smooth two-term
law with O(1) remainder is indeed excluded. This does not exclude the
unproved condition D(R)=o(log R), which is what the stated smaller second-term
remainder requires.

The optional power saving is also correctly scoped. The same logarithmic
lower bound gives ||h*theta|| bounded below by a constant times h^−mu.
The [Erdős–Turán inequality, TheoremIII](https://www.renyi.hu/~p_erdos/1948-02.pdf)
then bounds |D(R)| by a constant times R/K+K^mu. Taking K of order
R^(1/(mu+1)) gives some effective exponent eta>0, depending on the fixed
parameters. This error is larger than log R and supplies no second counting
coefficient. No useful uniform numerical exponent is established.

## Transfer to eight signed19 children

The helper inspects all eight signed20 source packets in the frozen
[equation-orientation census](complete74_equation_orientation_census.md).
At either scale, the only orientation changes are the auxiliary coefficient
and squared root. The retained protections are

    T2=(ic²)²=K=Delta(f²−1), U0=jc−r=U1=of−c.

Each norm uses C_e*(U_v²−y²)=1−y², C_e=T2 or K, U_v=U0 or U1.
The helper verifies these literal producers, both comparisons in all eight
packets, and equality of every other definition and interface within a scale.
Their comparison-zero sets consequently agree over every commutative ring;
the SOS-zero conclusion uses real ordered coordinates.

For each matching orientation pair the only changed producer is
X=wq³ versus X=wq. The helper checks all other definitions, comparisons,
ports, the unique w consumer, and q's independence from w. Substitution
w_new=q²*w_old preserves X and every later quantity. The complete r-consumer
inventory is r+1, jc−r, and the packing comparison. Therefore replacing r by
R=k−hXY−1 everywhere and deleting only the identical index comparison
commutes with this scale change. The corresponding full SOS identity follows
term by term, including the deleted zero square; different orientations are
asserted equivalent only on their protected zero loci.

The Report33 positive tuples thus give infinitely many negative-R zeros in
each of the eight corresponding nineteen-coordinate children at every
positive ordinary input. Only the forward scale map is needed. In the fixed
family, q and w are constants, so this changes one fixed coordinate and
preserves the eventual maximum y and the counting constants. It proves
neither an integral inverse on arbitrary asymmetric child zeros nor a
refutation of any twenty-coordinate positive-r parent. Raw29/positive21
and the distinct normalized/coupled unit-product interfaces remain outside
this statement.

After the report placement commits removed the incoming ZIP, recover its
authenticated historical bytes with the [archive replay guide](reviewed_report_archive_replay.md).
Use the resulting cache as the incoming directory; current proof/source pins
still refer to the live research tree. Replay from any directory:

    python3 /absolute/path/review_incoming_counterexample_heights.py \
      --root /absolute/path/native-stream-queue \
      --incoming /absolute/path/replay-cache/docs/incoming \
      --expect /absolute/path/review_incoming_counterexample_heights.json

The checker uses explicit failures and supports optimized Python. No
numerical giant witness, entire-fiber classification, new operation count,
or new polynomial degree follows from this receipt.
