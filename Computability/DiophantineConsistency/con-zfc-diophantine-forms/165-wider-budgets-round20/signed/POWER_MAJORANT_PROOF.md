# Independent audit of F=t^t at a cofinal even horizon

## Accepted result

The proposed replacement of F=(2(t+1))^t by F=t^t is valid in the
factorial-free architecture when the horizon is changed to t=16+2h^2.
This audit has read the incoming Factorial Free Binomial CRT report,
including the complete prime-power compiler, signed-bootstrap proof,
label-product argument, boundary y=F argument, and cofinal odd-square-beta
completeness. The result is relative to their named ordinary calibrations;
it is not a new formal-kernel endpoint. Literal graph/atom-list changes
need their separate finite audit.

## Equal counts and the strict coefficient bound

Let all positive labels lie in {1,...,t}, and W_j=1+jF. Discard all unit
label-zero factors from the label-product equality. The conclusion side
has at most t factors and the other side at most2t+1. If their counts
differ, let r be the smaller count. Then r<=t, the larger product is
at least(F+1)^(r+1), and the smaller is at most
(1+tF)^r<=t^r(F+1)^r. This is impossible because F+1=t^t+1>t^r.
So both sides have the same factor count d<=t.

Consider the two degree-d polynomials product_(i=1)^d(1+j_i z).
Every coefficient of degrees0 through d is a positive integer. At degree k,

    1 <= coefficient <= binom(d,k)t^k <= t^d <= t^t=F.

The middle bound uses binom(d,k)=binom(d,d-k)<=d^(d-k)<=t^(d-k),
with the trivial empty-choice bound1 when k=d; if d=0 both polynomials
are simply1. Therefore the difference of corresponding coefficients has
absolute value at most F-1, EVEN WHEN an individual coefficient equalsF.
The positivity of both same-degree coefficient lists is essential; an
argument bounding a coefficient byF alone would not justify base-F
uniqueness against a zero coefficient.

A nonzero difference polynomial cannot vanish atF: divide by the lowest
nonzero power ofF and reduce moduloF. Its first nonzero coefficient has
magnitude strictly between0 andF, contradiction. Hence the polynomials
are identical. Distinct factors1+jz have different roots-1/j, so unique
factorization gives exactly the required label multiplicities. The retained
single-conclusion Horn-flow lemma then gives the refutation.

## All other changed hypotheses

For t=16+2h^2, t is even and the allowed horizons remain unbounded, so a
finite proof tree can be padded to a permitted horizon. No requirement
for every integer horizon exists in the completeness argument.

The exact-power request at the already present positive base/index t gives
F=t^t>=16^16=2^64>2^32, independently of signs of other arithmetic inputs.
All retained numerical inequalities using F>=t, F>2^22, or F>2^32 hold.
For t>=2, t^t>t!, so with Lambda_t=lcm(1,...,t),
F>t!>=Lambda_t and the CRT radius R=F^2 satisfies R>=Lambda_t^2.
No divisibility ofF by t! is being asserted or needed for that compiler.

Since t is even, v_2(F)=t*v_2(t)>=t>v_2(t!). An arbitrarily large odd
multiple w of the odd part of t! makes y=F*w^2 an even multiple of t!.
The beta CRT moduli1+(i+1)y are therefore pairwise coprime and odd;
y can exceed every pending-multiset accumulator andF+1, and their common
code x can be chosen positive and even. This retains the old parity freedom.
The y=F boundary exclusion is unchanged: zero initial accumulator propagates
to a final accumulator that the last endpoint forces to be1.

For R=F^2, v_2(R)>=2t>floor(log_2 t), so v_2(R+i)=v_2(i) for
1<=i<=t. Therefore B=binom(R+t,t) is odd. N=B^x andN^2 are odd,
retaining all independent parity adjustments of CRT representatives and
the semantic anchor; the same q odd-square completion remains available.

The source frame must contain the ACTUAL new base t and all other actual
request atoms. Removing the obsolete base2(t+1) is a syntactic graph delta,
not permission to drop any still-required frame atom. Subsequent projections
must explicitly restore every eliminated coordinate and retain quadratic
residual degree.

## Independent review of the retained compiler lemmas

The denominator bound t*binom(t-1,i-1)|Lambda_t follows prime by prime:
each floor-valuation summand is0 or1 and vanishes above p^a>t.
If R>=Lambda_t^2, each R+i has some prime valuation v>2a with
a=v_p(Lambda_t); every other R+j has valuation v_p(j-i). Thus
v_p(B)=v-d>a, where d=v_p(t*binom(t-1,i-1))<=a, giving the required
row selector p^e>t dividingR+i. Conversely every prime p^e||B has a
compatible row because its Legendre valuation sum has at most one unit
per level up to max_i v_p(R+i), hence e<=that maximum. These two facts
address separate soundness and completeness obligations.

The range lemma p^e|binom(A,k) implies A mod p^e<k is valid: if the
k consecutive numerator factors contained no multiple ofp^e, the
Legendre zero-one terms at level e and above would vanish, giving total
valuation at most e-1. For soundness, apply it at p^(Ke) and compare
against the row selector >t; the local bound<2^K then turns its congruence
into equality. For completeness, prescribe compatible rows at EVERY prime
ofB modulo p^(2Ke); division byk! loses at mostk-1<K<=Ke and leaves the
required p^(Ke). No reciprocal-factor pairwise coprimality is used.
