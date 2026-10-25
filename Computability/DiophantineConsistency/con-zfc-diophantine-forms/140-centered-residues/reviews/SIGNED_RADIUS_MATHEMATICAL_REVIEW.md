# Independent review of the signed radius and odd-square reductions

## Verdict and scope

**Accepted as an ordinary mathematical reduction, relative to the explicitly
inherited signed source and its C222/ZFC-refutation calibration.** The three
new constructions preserve the existence of integer solutions. The most
compact reviewed endpoint has 258 unrestricted integer variables, 186
quadratic residuals, and a sum-of-squares polynomial of degree four with
5,366 collected monomials and coefficient height 128,446.

This review checked the previously vulnerable order of recovery: the
coefficient margin is proved before the factorial fixed point; signed powers
are recovered before a remainder is assumed positive; and the odd-square
completeness construction chooses all necessary parities simultaneously.
The weighted seven-member radius cap also satisfies the same arithmetic
lemma. No unresolved defect in these changes was found.

The input is `direct_proto/signed_source/factored_source.json`, with literal
file SHA-256

```
ef999ac4bb2296a450574f0536c72aaaedb48116523f84d25184dba18c1b39f0
```

The inherited proof boundary consists of the canonical signed Pell
orientation and power theorem, the source's literal constructor majorant,
the integral Horn factorization, and its C222/refutation interpretation.
The copied `PROOF_315.md`, `ORIENTATION_FIRST_PROOF.md`, and
`STRICT_BUDGET_PROOF.md` identify those dependencies. This review examined
their relevant hypotheses and the order in which they are supplied; it is
not a fresh proof-assistant formalization of the complete C222 calibration.

## 1. Recovery order, including the weaker initial bound on q

All raw coordinates range over the integers. The retained scalar sign
graphs imply only the two initial nonnegativities r,s >= 0. They yield

\[
B=r+s+1\ge1,\qquad BF=V+s.
\]

In the first radius variant, the old output guard still gives q >= B+1.
In the two odd-square variants it is replaced by

\[
q=(2z+1)^2,
\]

so initially one may use only q >= 1. This distinction matters: the
negative-index lemma at base q cannot yet be used in the latter variants.

The inherited orientation argument is independent of these removed
interval signs. The square frame bounds every actual power atom, and the
pooled small signed residues orient both coordinates of every principal
Pell pair. Consequently the canonical signed-power lemma applies to each
request as soon as its base is at least two. For base one it also applies
when the exponent is already known to be nonnegative.

The following order is valid even with only q >= 1:

1. The cofinal horizon t = 16 + h0^2 is positive. Its canonical pair
   interprets the request with base F^2+1 >= 1, giving
   V = (F^2+1)^t >= 1. The possible F = 0 case is covered by the known
   nonnegative exponent and base-one clause.
2. Since BF = V+s > 0 and B >= 1, F >= 1. Moreover V > F^2, so
   B > F, B >= 2, and V <= BF < B^2. Also
   y = V(V-1) > F+2.
3. Apply the negative-index exclusion to **N = B^x**, whose base is
   already at least two. This gives x >= 0 without assuming q > 1.
4. The first endpoint
   x = F+1+(y+1)u0 forces u0 >= 0, since u0 <= -1 would imply
   x <= F-y < 0. Hence x >= F+1 >= 2. The last endpoint
   x = 1+[1+(t+1)y]ut then forces ut >= 1 and
   x >= 2+(t+1)y.
5. Every actual independent CRT representative is the exponent of a
   request at base q+1 >= 2. The same signed-power theorem therefore
   makes all nine representatives nonnegative. A stored coordinate is
   shifted by one and is allowed to equal -1; positivity of that stored
   coordinate is never needed. Thus H0 = 1 + sum(a_i) >= 1.
6. The request at base BH0 >= 2 now gives q = (BH0)^x >= B^2.
   Therefore o = q-B-1 >= 0, restoring the deleted front guard whenever
   the old source is reconstructed.

All remaining power requests now have the requisite positive bases and
are interpreted exactly. The strict exponent K is x, so the endpoint bound
K >= 2+(t+1)y is available before factorial interpretation. There is no
use of a removed remainder sign in this sequence.

## 2. The uniform coefficient margin is available before F = t!

Put ell = 2^22 and U = BH0. From the preceding facts,

\[
U\ge2,\qquad q=U^K,\qquad
V\ge2^t\ge2^{16},\qquad
y\ge2^{16}(2^{16}-1)>2^{31}>\ell.
\]

Thus K >= 2+(t+1)y > ell*t+4 and K >= 6. None of these inequalities uses
F = t!, binomial decoding, or positivity of an encoded program index.

The retained literal constructor majorant for the derived label J is

\[
J\le(\max(1,a,b,c,d)+1)^\ell\le(2H_0)^\ell\le U^\ell.
\]

This version of the bound is valid when all ordinary representatives
vanish. That case must not be excluded using a later semantic theorem.

For every low coefficient j < k in the eleven remainder requests, the
bound binom(n,j) <= q/16 follows as follows.

* For an ordinary representative n <= H0, all lower indices k are at
  most K. Hence
  binom(n,j) <= max(1,n)^j <= H0^(K-1) <= q/B^K <= q/16.
  This also covers n = 0 and j = 0.
* For the derived label J, the lower index is t+1. Thus j <= t and
  binom(J,j) <= U^(ell*t) <= q/U^4 <= q/16.
* For the factorial numerator n = F^2+t, use the elementary inequality
  binom(z+h,j) <= (z+1)^h for z,h >= 1 and 0 <= j <= h.
  For j < h it follows from Pascal's identity and induction on h;
  for j = h it follows from
  binom(z+h,h) = product(i=1..h)(1+z/i) <= (z+1)^h.
  Consequently binom(F^2+t,j) <= V < B^2 <= q/16.

The last inequality also covers the coefficient at j = t that the old
factorial argument will subsequently interpret. It does not assume what
that coefficient is.

For D = q^k define the canonical residue

\[
r^0=\sum_{j<k}\binom njq^j.
\]

Since q > 16 and every coefficient is at most q/16,

\[
0\le r^0\le\frac{q(D-1)}{16(q-1)}<\frac D{15}.
\]

The coefficients are also below q, so this is exactly the least
nonnegative residue of (q+1)^n modulo D. The four denominator groups have
sizes 2, 5, 2, 2, at denominators q^t, q^(t+1), q^(y+1), and q^x.

## 3. Radius lemma and restoration of the old signs

Let D >= 17, let 1 <= m <= 7, and suppose arbitrary integers r_i satisfy

\[
r_i\equiv r_i^0\pmod D,\qquad 0\le r_i^0<D/15.
\]

The quadratic equation

\[
D^2=4\sum_{i=1}^m r_i^2+1+a^2+b^2+c(c+1)
\]

forces |r_i| < D/2, because c(c+1) >= 0 for every integer c. A noncanonical
representative has absolute value at least D-r_i^0 > 14D/15. Therefore
r_i = r_i^0 for every i.

Conversely the canonical residues give

\[
4\sum_i(r_i^0)^2<\frac{4m}{225}D^2
\le\frac{28}{225}D^2.
\]

Hence G = D^2-4 sum_i(r_i^0)^2-1 is a nonnegative integer. Every such G
has the form a^2+b^2+c(c+1): apply Legendre's three-square theorem to
4G+1. It is odd and congruent to 1 or 5 modulo eight, so it is not of the
excluded form 4^e(8h+7). Exactly one square in a three-square
representation is odd modulo four; dividing the two even entries by two
and writing the odd one as 2c+1 gives the required identity.

The kept numerator equations supply all the needed congruences, including
the factorial request whose quotient has the form qQ+B. Thus a new zero
has precisely the old canonical remainders. Set s_i = D_i-r_i-1 >= 0.
The nonnegative product r_i*s_i has another three-square representation,
which restores each old interval product guard. The removed variables
are private, so all other rows remain satisfied.

This proves soundness of the replacement. Conversely an old zero has
these canonical remainders, and the uniform margin supplies the new
radius witnesses. The first radius replacement is therefore an
existential equivalence on all shared coordinates.

## 4. Weighted merger of the first two groups

The exact power recovery gives D_hi = q*D_lo for
D_lo = q^t and D_hi = q^(t+1). Introduce two product wires

\[
u_i=qr_i\quad(i=1,2)
\]

for the two low-denominator remainders. If r_i is congruent to r_i^0
modulo D_lo, then u_i is congruent to q*r_i^0 modulo D_hi. Moreover
0 <= q*r_i^0 < D_hi/15.

One radius cap at D_hi can therefore contain these two weighted residues
and the five existing high-denominator residues. The lemma above applies
with m = 7. The cap recovers u_i = q*r_i^0, and q > 0 then recovers
r_i = r_i^0. Completeness follows by setting the product wires to their
literal values and representing the one nonnegative gap.

The two new wires cost two variables. Deleting one old three-witness gap
saves three. This yields one fewer variable and one additional quadratic
row. It does not require a new power request: the exact same-base,
consecutive-exponent relation is already present in the source.

## 5. Simultaneous parity choices for odd-square completeness

Soundness of the odd-square restriction was established in Section 1.
Completeness is not a pointwise transformation of every old zero, since
an old q need not be a square. Instead construct the source witnesses
from the same finite refutation using its cofinal freedom.

Choose the usual sufficiently large t = 16+h0^2, then F = t!,
V = (F^2+1)^t, and y = V(V-1). Here y is even and divisible by F.
All beta CRT moduli 1+(i+1)y are odd and pairwise coprime. Their product
is odd, so the required beta code x has an arbitrarily large **even**
representative in its CRT class. This choice precedes the definition of N.

The factorial digit is

\[
B=\binom{F^2+t}{t}=\prod_{i=1}^t(1+F^2/i).
\]

Because F is even and i divides F, each F^2/i = F(F/i) is even. Thus B
is odd, and N = B^x and N^2 are odd.

The nine independent representative classes are chosen modulo N^2.
The odd modulus permits either parity in each class. Choose a,b with
opposite parities. The literal anchor identity h = 1+a+b modulo two
then makes h even. For the dominant representative choose
a = a0+2N^2 or a0+3N^2, with 0 <= a0 < N^2, to obtain the selected parity
and simultaneously

\[
2N^2\le a<4N^2,\qquad h\ge2a^2\ge8N^4.
\]

Choose one other independent representative, for instance c, to have
the parity making H0 = 1+sum(a_i) odd. This does not change the anchor
parity, which depends only on a,b. All the nondominant positive
representatives can still be chosen at most 2N^2. Thus their size bounds
and the dominance required for the source's squared-cap and frame
construction are preserved.

Now BH0 is odd and x is even. Therefore

\[
q=(BH_0)^x=\left((BH_0)^{x/2}\right)^2=(2z+1)^2,
\qquad z=\frac{(BH_0)^{x/2}-1}{2}\in\mathbb Z.
\]

These parity choices occur in the required order: x before N, and the
independent representative parities after the odd modulus N^2 is known.
They preserve all inherited completeness hypotheses and all newly
required canonical residue bounds.

## 6. Independent exact artifact audit

`check_signed_radius_independent.py` imports no producer, projection
routine, or vendored verifier. It independently reconstructs the finite
algebra and checks:

* all eleven old interval rows and product sign rows from source guard
  metadata, their exact private-coordinate occurrence conditions, and
  every retained literal coefficient;
* the optional deleted output guard and inserted odd-square row;
* the exact same-base, consecutive-exponent license for the weighted
  merger, every product wire, all radius rows, and the complete census of
  fresh and deleted coordinates;
* every monic integral projection restoration, the retained rows, all
  degree bounds, and the omitted unconstrained coordinates;
* every translation with convention old = new+shift;
* every coefficient of the independently expanded sum of squared rows,
  including support size, exact degree, coefficient height, and liveness
  of every declared final variable.

Both normal Python and optimized Python runs passed. The complete
receipts are `signed_radius_independent_receipt.json` and
`signed_radius_independent_receipt_optimized.json`.

| Variant | Integer variables | Quadratic rows | Degree | Monomials | Height |
| --- | ---: | ---: | ---: | ---: | ---: |
| Four radius caps | 261 | 185 | 4 | 5,377 | 128,446 |
| Four caps and odd-square q | 259 | 185 | 4 | 5,361 | 128,446 |
| Weighted three caps and odd-square q | 258 | 186 | 4 | 5,366 | 128,446 |

The final equation-file SHA-256 digests, in the same order, are

```
b2d60b2b8e8a47c75cf19762fe0fa5d0159cc646ed08a0d6f2726c63d55f914c
8aa3d316df809e6c9f818060902ece09d088bb081d882ac534975439769b4dd4
36a30a3fb0696a8b02106cc5667b3eb33ef706bd81cc19dbb3d80c69c1846a5e
```

These finite exact checks authenticate the displayed polynomials and
their coordinate transformations. They do not establish unbounded
arithmetic by testing examples. Sections 1-5 supply the ordinary
mathematical review of the new unbounded claims; the named source theorem
supplies the inherited logical calibration. Composing them proves, in
ZFC, that each reviewed polynomial has no integer zero exactly when
Con(ZFC). No claim of global minimality or a newly completed end-to-end
formal proof is made.
