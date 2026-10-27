# Independent audit: adaptive matrix contraction at nine groups

## Finding

The proposed coefficient improvement is valid relative to the exact inherited
deformation, Hermite recovery, slope-four pair-mode, and asymmetric-packing
interfaces. It changes the normalized wire-time coefficient from
35.354588058401... to 34.325282797285... and the corresponding space coefficient
from 34.274803005023... to 34.024178007491... . It does not change the power of
the logarithm in the SAT bound and is not a polynomial-space result.

The new local aggregation is substantively different from simply retuning the
existing cached-tree schedule: choose a partition into triples from exact pair
list sizes, and use an average/variance certificate for its final matrix
multiplication. Binary table construction then sets the local exponent.

A subsequently derived companion result in adaptive_separator_proof.tex
retains polynomial space and gives coefficient 50.210434836331... against the
previous 55.709478318910... . It selects the streamed binary separator tree
from the pair-list sizes using a separate second-moment calculation. Its exact
finite covariance and coefficient checks are in verify_separator.py and
separator_results.json. The remainder of this review concerns the cached
nine-group branch unless explicitly stated otherwise.

The root's subsequent subset-DP selector for the polynomial-space branch is
also correct. For each power-of-two subset S, precompute internal edge weight
W(S), set F({v})=0, and minimize
W(S)-W(A)-W(B)+max(F(A),F(B)) over equal-size splits A,B. The cut at S is
common to every descendant leaf path; ancestral cuts are common additive
constants too. Independent optimization of the two subtrees therefore gives
the exact minimum maximum path cost. Sixteen groups require 14,827 relevant
states and 462,465 unordered balanced splits, rather than factorial tree
enumeration. With b_e=ceil(log_2 N_e), rounding adds less than 170 bits to a
full leaf path. This preserves the proven coefficient and uses polynomial
space, because the subset universe is fixed and weights have polynomial bit
length. For eight groups, the analogous counts are 107 states and 273 splits;
the 315 complete balanced trees provide an independent exhaustive oracle.

## Cost ledger

Use r=9 and K(M,u)=pi sqrt(2) M/(ln(2) sqrt(u)). Each directed pair e has a
list of exact-budget mode exponents of size exp_2(h_e), with h_e nonnegative.
The imported joint entropy bound implies ||h||_2 <= (1+o(1))K/9. This follows
even if that bound was initially stated for each fixed nonnegative weight
vector: a finite epsilon-net of the nonnegative unit sphere proves the norm
bound, and epsilon can tend to zero after the asymptotic limit. Thus no hidden
uniformity in a budget-dependent direction is needed.

Combine the two orientations of each unordered pair as w_ab=h_ab+h_ba.
Then q=sum(w_ab^2)<=2K^2/81+o(K^2). Write W=sum(w_ab). For a uniformly chosen
partition into three triples let A,B,C be the three block-pair log dimensions,
and H=A+B+C. The exact partition moment identities give E(H)=3W/4 and

E[(A-H/3)^2+(B-H/3)^2+(C-H/3)^2]
 <= (27/28)(q-W^2/36).

The square-matrix exponent 12/5, extended by blocking, costs
G=H-(3/5)min(A,B,C). Since min(A,B,C)>=H/3-sqrt(2/3)*sqrt(sum deviations^2),
Jensen's inequality and a two-dimensional Cauchy inequality imply

min_partition G <= E(G)
 <= (3/5)W + (9/(5 sqrt(14)))sqrt(q-W^2/36)
 <= sqrt(57/175) K+o(K).

This coefficient is approximately 0.570713838727. The covariance matrix for
the 36 unordered edges has diagonal 1/2, adjacent-edge entries 1/28, and
disjoint-edge entries -1/21. Its eigenvalues are 0 on constants, 27/28 on the
8-dimensional standard vertex component, and 8/21 on the 27-dimensional
remaining component. This verifies the required quadratic inequality.

All 280 unordered partitions can be enumerated, a constant independent of s.
The optimizer does not need transcendental computations. Replace each h_e by
b_e=ceil(log_2 |I_e|), determined from the bit length of |I_e|-1. Every pair
changes by less than one bit, and all objectives consequently change by O(1).
Choose the partition minimizing the integer objective 5(A+B+C)-3min(A,B,C)
with these rounded edge weights. The norm bound changes by at most sqrt(72),
also O(1), so the same asymptotic coefficient is valid. Alternatively, for
positive block-pair products N1,N2,N3, compare the exact rational expressions
(N1*N2*N3)^5/min(N1,N2,N3)^3. Empty pair lists cause their whole budget array
to vanish before partition selection.

Each singleton group cache has 16 incident directed pairs and hence uses at
most exp_2((4/9+o(1))K) expensive recursive child contractions. A pair table
is built from two singletons with class cardinalities (14,2,14); its matrix
cost squared, before division by 9^2, is 30-(21/25)*2=708/25. A triple table
is built from a singleton and a pair with cardinalities (12,4,24); its cost
is 40-(21/25)*4=916/25. The final adaptive triangle cost is lower. Therefore

alpha=4/9,
beta=sqrt(916)/45=0.672566486685...,
j=2/3,

and the local recurrence is

T_d <= poly(s)*[2^((alpha+o(1))K_d)T_(d+1)+2^((beta+o(1))K_d)].

The largest stored table is a triple boundary with 36 directed pairs, giving
j=2/3. The matrix operands, output, and temporaries have no larger exponent.

## Schedule audit

Let lambda=ceil(log_2 s), b=ceil(6 log_2 lambda), and

J=max{j>=0:9^(20j)<=2^lambda},
U=J-ceil(sqrt(lambda)),
u_d=floor(U/2^d),
a_d=sum_(h=0)^d u_h+(d+1)b,
H=ceil(s/lambda).

Small sizes or nonpositive U are treated by direct summation. All comparisons
in J can be implemented with polynomial-bit integers. The limiting U/lambda
is 1/(20 log_2 9). The root's symmetric packing condition involves Q^2 Delta,
where Q=9^(a_0) and Delta<=ceil(s^(9/10)); its base-two log is at most

lambda-2 log_2(9) sqrt(lambda)+O(log lambda).

Below the root, the retained side has degree at most s^(9/10+o(1)); the fresh
opposite side has degree at most 2^(a_(d-1)+1). Since sum u_d<=2U, the
high-degree asymmetric term Q*Delta has the same square-root-lambda slack,
up to O((log lambda)^2). The fresh-side and padding terms Q^2*C and 2^a Q^2
have exponent at most

(2 log_2 9+1)/(10 log_2 9) lambda+o(lambda)<0.232 lambda.

Thus all three near-lossless-packing gates hold uniformly on active calls
with M>H. To avoid circular reasoning, bootstrap only depths
d<=ceil(log_4 lambda)+O(1). In this range u_d=lambda^(1/2+o(1)) tends to
infinity, and a_d has the preceding bounds. Packing gives child ratio
2/9+o(1)<1/4, closing the bootstrap. Its sharper uniform ratio gives

M_d<=(1+o(1))^d s(2/9)^d.

At each retained interpolation level, D>=2^(a_(d-1)+b+1). Inherited precision
is O(s lambda^2 2^(a_(d-1))), and its ratio to MD/u is at most
O(lambda^4 2^(-b))=o(1). The local Taylor-evaluation loss is likewise lower
order. Therefore p_t<=(6+o(1))MD/u holds uniformly at every active depth.

Set kappa=pi sqrt(40 log_2 9)/ln 2 and gamma=2sqrt(2)/9. Then
K_d <= (kappa+o(1))gamma^d s/sqrt(lambda) uniformly. Since

alpha/(1-gamma)=4/(9-2sqrt(2))=0.64813... < beta,

the full recurrence is controlled by the root nonrecursive term. A path
ending in local work at depth d has coefficient
alpha sum_(h<d)gamma^h+beta gamma^d<=beta. A path ending at a leaf has no
larger coefficient. Polynomial factors accumulated over O(log lambda)
depths add O(lambda log lambda), which is negligible.

The resulting coefficients are

C_T=pi sqrt(40 log_2 9)*sqrt(916)/(45 ln 2)=34.325282797285...,
C_S=2pi sqrt(40 log_2 9)/(3 ln 2)=34.024178007491... .

Ancestor table storage adds sizes rather than multiplying them, so the root
also controls space. Leaf work 2^O(s/lambda), original entry work 2^O(s^.9),
and new packet entry work exp(O(2^a log s)) are lower order on this scale.

## Ring and recursive-oracle audit

The matrix backend is applied to the actual finite free module
(Z/2^p Z)[U,V]/(f(U),V^ell), not incorrectly to a field. For every pair of
module coordinates, lift inputs to nonnegative integers, multiply their
ordinary integer matrices modulo polynomially many small nonexceptional
odd primes, and reconstruct by CRT. An entry of an unreduced integer product
has at most 2p+ceil(log_2 d2)+1 bits, polynomial in s. The fixed rational
bilinear algorithm of exponent strictly below 12/5 has finitely many fixed
exceptional denominator primes; omitting them is valid. Coordinate pairs,
structure constants, CRT storage and exact field arithmetic introduce only
polynomial factors. Depth-first recursion for a fixed finite bilinear scheme
uses quadratic matrix storage. Rectangular blocking yields d1*d2*d3 /
min(d1,d2,d3)^(3/5), which is precisely the cost G above.

Each cached group function depends only on the incoming and outgoing pair
mode indices incident to that group. The immutable source packet description
and creation precision make this dependence exact. Each table entry pays for
one real child contraction; no child oracle is assumed free. The enumeration
of exact pair-weight arrays costs at most a fixed polynomial (r=9 is fixed),
and descriptions remain polynomial. New grouping changes only the ordering
of finite sums and products and uses no illicit lifting of a residue.

## Limitations

The result does not supply an end-to-end SAT implementation or a new formal
proof. It preserves all upstream algebraic assumptions. Its time gain is
exp_2((1.0293052611+o(1))*s/sqrt(log_2 s)) between the displayed upper-bound
certificate functions. It is not a measured runtime ratio, and the constants
are per normalized Boolean wire, not per SAT variable. The unrestricted SAT
order remains n log log n/sqrt(log n).
