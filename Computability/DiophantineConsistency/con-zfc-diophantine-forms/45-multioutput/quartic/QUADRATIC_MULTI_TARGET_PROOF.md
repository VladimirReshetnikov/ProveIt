# Encoding the 22 quadratic residuals without taking their sum of squares

## The fixed finite data

Let r_1,...,r_22 be the residuals of package31's 60-operation system, after
simultaneously substituting n_i+1 for its 31 positive variables. Thus all
n_i range over nonnegative integers. Every residual is quadratic. The
source's original fifth residual is E-X(a-E); after shifting its constant
coefficient is 1. Order the rows as

  1,2,3,4,6,7,...,22,5.

The last row therefore has constant coefficient 1, independent of all four
compiler ports. `QUADRATIC_TARGETS.json` records all 136 nonzero shifted
residual terms, their symbolic coefficients, weights and target positions.
The terms are reconstructed independently by `verify_quadratic_targets.py`.

The fixed weights, in the source's 31-variable order, are

  10,35,55,62,105,144,145,159,168,232,245,306,323,325,353,
  371,374,382,494,499,525,566,578,610,647,681,685,741,777,783,799.

With padding weight 0, all 528 two-element multisets have different sums
modulo 1023, and hence different ordinary integer sums. Consequently these
weights distinguish every monomial of total degree at most two. Let W=799,
S=2W+1=1599 and H_j=jS for 1<=j<=22. The last target is H_22=35178.

## Multi-target extraction theorem

Write each reordered residual as r_j(X)=sum_alpha p_{j,alpha} X^alpha,
where |alpha|<=2, and let w(alpha)=sum_i alpha_i w_i. Define

  D(T)=sum_{j=1}^{22} sum_alpha
        (2-|alpha|)! product_i(alpha_i!) p_{j,alpha}
        T^(H_j-w(alpha)).

For every integer tuple x, the coefficient of T^(H_j) in

  D(T) (1+sum_i x_i T^w_i)^2

is exactly 2 r_j(x), simultaneously for every j.

Proof. A term from source row k and monomial alpha, multiplied by a
multinomial expansion term beta, reaches target j precisely when

  H_k-H_j = w(alpha)-w(beta).

The right side has absolute value at most 2W. Any nonzero left side has
absolute value at least S=2W+1. Thus k=j. The B2 property now gives
alpha=beta. The product of the two factorial factors is 2, proving the
claim. This establishes the assertion for every integer x, not just a
bounded test domain.

The interval of possible exponents in the jth portion of D is
[H_j-2W,H_j]. These intervals are disjoint. Within each interval, the B2
property gives distinct exponents. Hence every coefficient of D is a
single weighted source coefficient. If |p_{j,alpha}|<=M, its absolute
value is at most 2M. Moreover the coefficient of its highest exponent
35178 is exactly 2, because the last residual's constant coefficient is 1.
Therefore D(B)>0 for every integer B>2M+1: the possible negative lower
coefficients have magnitude less than

  2M(B^35178-1)/(B-1) < B^35178,

whereas the leading term is 2B^35178. This is a mathematical sufficient
bound, not a claim that the materialized base is that small.

For every output exponent e, the coefficient of the product has absolute
value at most

  2M(1+sum_i |x_i|)^2.

Indeed, for a fixed multinomial term beta, the required exponent in D is
e-w(beta), and at most one pair (j,alpha) occupies that exponent. Sum the
bounds over all beta using the multinomial theorem. There is no extra
factor 22. Distinct source blocks are important for this bound.

These are formal-coefficient statements and magnitude bounds. The complete
arithmetic bridge must additionally enforce that *every* target coefficient
is zero without allowing cancellation between different targets. A check
of their unweighted sum is insufficient. The main report's multi-target
arithmetic mask and extraction theorem are separate obligations; this note
does not silently identify a formal coefficient with a base-B digit in the
presence of carries.

## Explicit B2 construction and finite certificate

Use GF(2^10) with the bit polynomial 1033, namely X^10+X^3+1, and theta=X.
The constructor checks that theta has order 1023 by enumerating all its
powers without repetition. Since 1023=3*11*31, this also witnesses the
full multiplicative group. The subfield GF(32) consists of 0 and the 31
powers of theta^33=620. Direct exponentiation verifies a^32=a for all of
these 32 distinct elements.

The Bose--Chowla residues are log_theta(theta+a), a in GF(32). Two equal
pair sums modulo 1023 would give equality between the products of two
linear polynomials theta+a. Their monic quadratic terms cancel, leaving a
polynomial of degree at most one over GF(32). Since theta is not in that
subfield, both coefficients vanish. The two multisets of a's are equal.
This proves the B2 property. Translation of every residue and multiplication
by a unit preserve fixed-length pair-sum distinctness. Multiply by 47,
translate by -879 modulo 1023, and sort to obtain the displayed set with
padding 0. The largest circular gap is 224, so the largest representative
is 1023-224=799.

`build_b2.py` reproduces the field construction and exhaustively searches
all unit multipliers and circular cuts of this one affine orbit. Its claim
of an optimal gap concerns only that finite orbit, not all B2 sets. The
delivery verifier need not trust the construction theorem or optimizer:
it directly checks the 528 pair sums of the delivered small integer vector.

## Independent replay

`verify_quadratic_targets.py` uses only the Python standard library. It reads
the source circuit as JSON data, checks its byte digest, evaluates its
registers in an independently written sparse polynomial ring, and applies
the 31 shifts at the inputs. It verifies all 136 symbolic coefficients,
the factorial weights, all target exponents, the last coefficient 2 and
all 71,808 source-term/expansion-monomial pairs for target contamination.
No upstream script is executed, and no bounded enumeration of Diophantine
witnesses is used as a substitute for the mathematical proof.
