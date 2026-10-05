# Independent review of the nine-gate index/transport cut

**PASS for the exact joint product at the declared nine-input cut.** Root
read the complete proof note and the actual 84-row parent source as inert
data. The bound does not apply to a source using further donor registers
or a polynomial that merely preserves positive zeros.

The author note is pinned at
`0dc78b19b5f7c566dd944d1a307d70311b135d9cff062c6c43bf095750030d7f`.
The parent JSON remains
`8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`.

The exact target is

    (k-R-hE)*((K+w)C+U-tr),

with K fixed and nonzero. The selected parent rows cost 3M+5A and
forming their product adds one multiplication. Reassociating the two
downstream factor products preserves their total cost. Root checked each
row and its consumers; no common predecessor is being deleted for free.

The proposed rational inverse of the cut is correct. In particular the
actual source gives E=w*s*q^4 and
R=(qU-Z)(q²-1)+(MC+q*MF)Jrep. Solving successively for Jrep,F,Z,alpha,s,zeta
recovers the nine independent cut coordinates on a nonempty open set.
MF keeps the supplied shifted convention. These rational expressions
prove algebraic independence only; they are not integer source gates or
positive witness restoration formulas.

The support-difference lower bound is valid with reuse: keep one vector
space containing every wire's support differences, allow each wire its
own affine translate, and add at most one direction per sum. Products
add no direction. The six displayed monomials of the target yield five
independent differences; projection to R,h,w,U,t gives the identity matrix.
This proves at least five additions/subtractions independently of the
number of multiplications.

Root separately challenged the three-multiplication classification while
granting every affine operation free. The first genuine product has a
decomposable quadratic leader Q1. If the second gate has degree two, both
available quadratic leaders are decomposable; dependent leaders give no
second quadratic direction. A quartic from the third gate must then be a
product of two quadratics in their span. Unique factorization of
`-hE(wC-tr)` forces that span to be `span(hE,wC-tr)`. Its only decomposable
quadratics are multiples of hE, because any nonzero determinant component
has symmetric rank at least four. This is a contradiction.

If the second gate has degree three, the possible quartic leaders at the
third gate are four linear factors or Q1². If it has degree four, its
leader is proportional to Q1²; a third gate of higher degree cannot have
its leader canceled by earlier outputs, while another quartic can only
have the same square leader. Canceling those leaders drops degree. None
can produce the target's irreducible quadratic factor wC-tr. Thus all
degree and cancellation cases leave at least four genuine products.

Both lower bounds apply to the same arbitrary circuit, so the current
4M+5A schedule is optimal at this exact cut. Nonzero scalar multiples have
the same conclusion. Arbitrary polynomial multipliers, additional donors,
cross-factor sharing and positive-zero-only replacements remain outside
the theorem. In particular the result does not prove a universal lower
bound of 84 operations.

The companion JSON checks pins, literal rows and private consumers by
fresh metadata code only. No parent/helper/source array was executed,
imported or expanded; no finite sample stands in for the lower-bound proof.
