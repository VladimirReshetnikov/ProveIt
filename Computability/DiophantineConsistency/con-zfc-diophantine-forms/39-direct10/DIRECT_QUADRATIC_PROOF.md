# Direct quadratic multi-target coding into Sun's ten-integer equation

This note proves the new encoding step. The final Lucas bridge and three-radical
norm are the unchanged formulas of package 31, `signed10/SIGNED10_PROOF.md`, at
ProveIt commit `22e75dd6b87b1b199bb08c778d7cf075ae5aae08`. The primary imported
results are Sun 2021 (arXiv:1704.03504v7), Lemmas 2.2 and 2.4 and the bridge
estimates in Theorems 4.12--4.13, and Sun 2026 (arXiv:2609.01594v2), Sections 3--7.
The replacement below supplies exactly the source hypotheses those results use.

## 1. Source and indexing

Let the fixed, calibrated package-30 parent have positive coordinates

`J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta`.

Its 22 quadratic residuals are defined exactly by `data/parent_quartic31.json`.
Replace every positive coordinate by one plus a nonnegative coordinate. Write the
resulting residuals as `r_j(n)=sum_alpha p_{j,alpha} n^alpha`, degree at most two.
Their common zero set is unchanged by reordering. Move residual 5 to the end, so
that channel order is `(1,2,3,4,6,...,22,5)` and the last residual has constant
coefficient +1. This follows directly from `E-X(a-E)` at all original coordinates
one. In particular the all-zero nonnegative tuple is not a common zero.

Use the 31 positive weights

37,111,124,146,228,259,285,304,306,312,329,336,404,422,432,
493,555,566,607,645,646,649,661,695,704,709,776,816,845,881,901.

Together with zero they have 528 distinct unordered pair sums. Thus if
`|alpha|,|gamma|<=2` and `alpha.w=gamma.w`, then `alpha=gamma`: pad the two
multisets by zeros to length two. This is a complete finite certificate, not a
probabilistic test. The weights can also be reconstructed by the Bose--Chowla
construction in GF(2^10); the finite check suffices for every theorem here.

Put `t=901`, `r=22`, `q_j=2t+j(2t+1)` for `0<=j<22`,
`Q=q_21=39665`, `h=Q+2t=41467`. Define

`c_{j,alpha}=(2-|alpha|)! product_i alpha_i! p_{j,alpha}`,

`D(Z)=sum_j sum_|alpha|<=2 c_{j,alpha} Z^(q_j-alpha.w)`.

Each exponent is nonnegative. The exponents within each channel are distinct.
Channel j occupies the interval `[q_j-2t,q_j]`, so distinct channels have disjoint
coefficient intervals. If `L>=max |p_{j,alpha}|`, every coefficient of D has
absolute value at most `2L`. Its leading coefficient is exactly 2, since the
last residual has constant +1 and every weight is positive.

## 2. The new simultaneous coefficient identity

For any nonnegative n, let `C(Z)=(1+sum_i n_i Z^w_i)^2`. Then

`[Z^q_j] C(Z)D(Z) = 2 r_j(n)` for every channel j.

Proof: inside one channel the distinct pair-sum property selects exactly the
matching multi-index, and its multinomial coefficient cancels the factorial
weight, leaving `2 p_{j,alpha} n^alpha`. A different channel k contributes to
powers only in `[q_k-2t,q_k+2t]`. Since different centers differ by at least
`2t+1`, no such interval contains q_j. This proves the identity. Notice that
squaring the residuals is unnecessary: their different target digits retain
all equations separately.

Also `deg(CD)<=h`. Since C has nonnegative coefficients,

`abs([Z^s]CD) <= 2L (1+sum_i n_i)^2` for every s.

The bound has no factor of 22: each coefficient of D belongs to exactly one
channel. The degree of D and its coefficient bound are fixed independently of n.

## 3. Fixed source constant

Use the complete native tuple `wang943-mixed-121x8801` from package 31, without
mixing its ports with another tuple. The port order and bit lengths are
`beta:1064921`, `K0:1070004`, `MC:1064921`, `MF:1064922`.
The fourth port already includes the shift by native B-1.

For each symbolic ordinary coefficient `p=sum_e a_e port^e`, bound its absolute
value by `U(p)=sum_e abs(a_e) 2^(sum_i e_i bitlength(port_i))`. The maximum U over
all 22 shifted residuals has bit length 2,134,926. Exact integer arithmetic
verifies

`beta_S := 2^2134938 > 4*33^2 * max_p U(p) >= 4*33^2 L`.

The exponent is even. Its exact binary payload and the complete coefficient
recipes are provided; no existential coefficient or recursively enumerable
index is hidden here. Seventeen fixed circuit leaves suffice, including beta_S.

## 4. Source polynomials in f and g

All these are polynomial abbreviations, not new unknowns. Set

`b=1+3f`, `B=beta_S b^2`, `ell=sum_i B^w_i`,
`N0=B^(t+1)`, `N1=4B^(h+1)`, `N=N0N1=4B^42370`,
`M=N0-1-(b-1)ell`, `A_targets=sum_j B^q_j`,
`T=M+(B-2)A_targets N0`,
`J=2(1+g)^2 D(B)+B sum_(s=0)^h B^s`,
`S=g+JN0`, `R=(S+T+1)N+T+1`,
`X=(N-1)R`, `Y=N^2`, `cap=bB^t`.

The cap has the prescribed monomial form
`2^1923579138 b^1803`. All powers and summation limits are fixed natural numbers.
Their division-free circuit is emitted in `generated/direct10.json`.

### Range and divisibility facts before assuming b is a power of two

Suppose f is nonzero, b is an integer square, and `0<=g<2 cap`.
Because `b=1 mod 3` and b is a square unequal to 1, b>=4 and f>0. In particular
B is a positive even integer. We have `0<=M<N0` by the displayed base-B digits.
Also `(B-2) A_targets < B^(Q+1) <= B^(h+1) < N1`, so `0<=T<N`.

The leading coefficient of D is 2, and all others have magnitude at most 2L.
Because B>2L+1,

`abs(D(B)-2B^Q) <= 2L sum_(s=0)^(Q-1) B^s < B^Q`,

hence D(B)>0. On the other hand,
`D(B)<=2L sum_(s=0)^Q B^s`. Since `1+g<=2bB^t` and
`16L b^2<=B-2`,

`0<J<2B^(h+1)<N1`.

One obtains the strict upper bound by putting the two geometric sums over
`B-1`: their numerator is at most `(B-2+B)B^(h+1)`, strictly below
`2(B-1)B^(h+1)`. Also `g<2bB^t<=N0`, hence `0<=S<N`.
Consequently `R>=N+1`, `X>=N^2-1>3b`, and `Y=N^2>max(b,256)`.
As beta_S is an even power of two and b=1 mod3, B=1 mod3, so N=1 mod3 and
`3|X`. These are the source size and congruence conditions used by Sun's bridge.

### Carry equivalence when b is a power of two

Now assume in addition that b is a power of two. Then B,N0,N are powers of two.
Write `tau_2(u,v)=0` for addition without a binary carry (equivalently `u&v=0`).
Sun's general low digit-mask lemma, or direct binary expansion, gives

`0<=g<2cap and tau_2(g,M)=0`

iff `g=sum_i n_i B^w_i` for a unique tuple `0<=n_i<b`. The low digit range is
valid because `b<=2b<=B`.

For such a tuple, form C as above and put

`J'=C(B)D(B)+(B/2)sum_(s=0)^h B^s`.

Its actual base-B digits are
`e_s=B/2+[Z^s]C(Z)D(Z)`.
Indeed `0<e_s<B`, since

`abs([Z^s]CD)<=2L(1+sum_i n_i)^2<2L(33b)^2<B/2`.

No carries or borrows occur in this digit description. Because B is a power of
two, the binary mask `(B/2-1) B^q_j` tests all but the leading bit of digit e_qj.
That digit is in `(0,B)`, so it passes exactly when it is B/2. The target blocks
are disjoint. It follows that

`tau_2(J',(B/2-1) A_targets)=0`

iff every `r_j(n)=0`. Multiplication of both arguments by 2 preserves absence of
binary carries; since J=2J', this is also

`tau_2(J,(B-2) A_targets)=0`.

Because `g,M<N0`, splitting the concatenated low and high words gives

`tau_2(S,T)=0`

iff `tau_2(g,M)=0` and `tau_2(J,(B-2)A_targets)=0`.
Finally, the general carry-to-binomial lemma (Sun 2021, Lemma 2.2, p=P=2) gives

`tau_2(S,T)=0 iff N^2 divides binomial(2X,X)`.

Thus the reverse source implication is proved with precisely the hypotheses
used by the existing ten-integer bridge.

## 5. Completeness and handoff

If the 22 residuals have a nonnegative common zero n, then n is nonzero because
r_5(0)=1. Choose a sufficiently large `b=4^s>max_i n_i` and
`f=(b-1)/3`, which is a positive integer. Encode `g=sum_i n_i B^w_i`.
Then `b<=B<=g<cap`, and every carry test above vanishes. Therefore
`Y | binomial(2X,X)`. The choices can be made arbitrarily large.

Conversely, the source square, power, range, nonzero and binomial divisibility
hypotheses yield a unique nonnegative common zero of all 22 residuals.

This is exactly the two-way source contract required by the package-31
modified Sun bridge. Substitute the X,Y,cap just constructed in that bridge;
keep its remaining polynomial formulas unchanged. The existing coprime
positivity merger, quintic divisibility merger, separating weights and
three-radical norm then yield a polynomial F in the ten unrestricted integer
unknowns `f,g,h,k,l,w,x,y,z,m` such that

`exists_Z^10 F=0 iff exists_N^31 all r_j=0 iff a finite ZFC refutation exists`.

Every step is finitary ordinary mathematics formalizable in ZFC; the statement
does not use consistency to prove its own equivalence. Negation gives
`ZFC proves: (no integer zero of F) iff Con(ZFC)`.
No new end-to-end Lean/Rocq certificate is asserted. Finite checks certify the
literal source, all 528 pair sums, the symbolic target identities, coefficient
bounds, exact emitted circuit, and attained polynomial degree.

## 6. Quantitative claim and boundaries

The emitted division-free circuit uses 786 binary operations:
222 additions, 25 subtractions and 539 multiplications. It has 17 fixed leaves.
Its degree bound is 267,823,432; the nonzero leading coefficient audit makes
this an exact degree (see the verification receipt).

Compared with package31's ten-integer equation: unknown count is unchanged;
degree falls from 589,042,901,992,797,851,562,527,064 to 267,823,432 (a factor
about 2.20e18); operations fall from 1442 to 786 (45.49%). This is an improvement
of that concrete ten-integer equation, not a claim about universal optimality
or about the best positive-domain nine-variable or low-degree high-variable
forms. The additive-combinatorial construction of B2 sets is classical; the
new contribution here is its combination with simultaneous carry testing of
the fixed quadratic system, bypassing its quartic sum of squares.
