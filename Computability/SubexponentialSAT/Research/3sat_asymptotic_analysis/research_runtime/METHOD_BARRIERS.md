# Restricted barriers; not lower bounds for 3SAT

Pin: 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a.
Sources: source/build/quantitative-contraction.tex and quantitative-reduction.tex.

## 1. Mode-budget counting is tight from its numerical information alone

Let u grow, D/sqrt(u) grow, and D <= M. Suppose a formal mode catalogue has
k=floor(M/D) variables of each positive integer weight. For a fixed positive
c let p=c MD/u and choose W=floor(eta D/sqrt(u)), with eta>0 sufficiently
small depending only on c. The total weight of ALL kW variables with weights
1,...,W is k W(W+1)/2 < p. Every zero/one subset of them is therefore feasible.
There are 2^(kW)=2^Omega(M/sqrt(u)) such tuples. Every one has ordinary degree
at most kW=O(M/sqrt(u))<M. The rounding is harmless since k>=M/(2D) and
W>=eta D/(2sqrt(u)) eventually. The standard generating-function estimate
provides the matching exp(O(M/sqrt(u))) upper bound when multiplicity is
O(M/D) and p=O(MD/u).

If weights are shifted to b+v, where v=O(log D), the sum receives an extra
kW v=O(M logD/sqrt(u)). This is negligible relative to p whenever
sqrt(u) logD / D -> 0, as in the active-call parameter regime. Thus the true
initial coefficient valuation a+1-i does not, alone, improve exponent order.

This constructs a formal catalogue saturating the bound. It is not a proof
that every actual input realizes all these modes, that their coefficients
are nonzero, or that no different algorithm can sum them faster. It proves
that constraints on per-weight multiplicity, weighted budget, and ordinary
degree alone cannot justify the proposed smaller worst-case enumeration
bound. Distinct-part (zero/one) restrictions alone do not remove the barrier.

## 2. Monotone taper precision has a 1/u scale

Assume nonincreasing multiplicities q_0 >= q_1 >= ... >= q_u=0,
with q_0 >= c M, c>0 fixed. Some i<u has q_i-q_(i+1)>=cM/u.
In the source identity
-v2(E_t(0))/D_t = sum_(j>=1) (j/2^j)(q_i-q_(i+j)),
all summands are nonnegative; its j=1 term alone is >=cM/(2u).
Thus at one retained level the displayed Hermite multiplier has valuation
at most -c MD_t/(2u). A coefficientwise independent-error accounting of
these multipliers cannot replace the precision-loss scale MD/u by o(MD/u).
This is restricted to monotone profiles and the current recovery/accounting;
it is not a lower bound against correlated-error reconstruction or a new
interpolation scheme. With the total jet degree condition and monotonicity,
q_0=Omega(M) is forced because fewer than 2L nodes are used to cover degree
M(2L-1).

## 3. Direct batching of beta is not licensed by Theorem D.1

A candidate encoding groups beta variables by source-target pair, allocates
weight budgets, and uses B=O(M/sqrt(u)) bits to index the feasible tuples.
Its r group tensors would have entries Z_(g,beta), each evaluated by a child
contraction. With fixed r, average degree is 2B/r=Theta(B), violating the
published maxdegree B^0.9. These tensors are arbitrary group-contraction
functions, not equality tensors, so equality-tree degree reduction is not
valid. Their entry oracle costs also exceed D.1's exp(O(B^0.9)) allowance;
that hypothesis needs a separate multiplicative-oracle-cost extension.

Growing r offers no immediate asymptotic gain even if oracle work is handled.
The first packing condition is M >= 2 r^(4a) Delta, and u<=a. Hence
u_first=O(log M/log r) for original Delta>=1. Its first-stage code majorant is
B about M/sqrt(u_first), losing a factor sqrt(log r) compared to fixed r.
A second network on r vertices has Delta' >= 2B/r; its packing gap allows
only O(log(B/Delta'))=O(log r) taper levels with a fixed new group alphabet.
The resulting B/sqrt(u_second) scale cancels the first loss, returning
M/sqrt(log M). This is a parameter obstruction within the same packing and
mode-enumeration design, not a lower bound on all possible batching.

## 4. Sparsification retuning alone does not remove loglog

Even an optimistic cost model n[sigma + c log(1/sigma)/sqrt(lambda)], where
lambda=log n and c>0 fixed, minimizes at sigma=c/sqrt(lambda) (when interior).
Its minimum is Theta(n log lambda/sqrt(lambda)). Equivalently, making the
branching term as small as the published target forces
log(1/sigma)=Omega(log lambda). Thus replacing one inverse-polylogarithmic
sparsification schedule by another cannot by itself remove the loglog factor.
This is a model-specific optimization, not an information-theoretic claim.
