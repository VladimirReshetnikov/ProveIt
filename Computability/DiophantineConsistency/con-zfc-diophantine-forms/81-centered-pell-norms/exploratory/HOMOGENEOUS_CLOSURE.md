# Eliminating the index coordinate from inert-prime CRT closure

Research component, 23 October 2026.  This is a proved compiler lemma, not a
completed new fixed Con(ZFC) polynomial.  Its input is an arbitrary explicit
integer polynomial.  The result sharpens source 75's certificate interface by
removing one existential coordinate and one norm leaf.  Factorial, binomial,
remainder and variable-exponent graphs still have to be compiled before this
can be reported as an ordinary Diophantine endpoint.

## 1. Exact input and notation

Fix a polynomial R(i,w_1,...,w_m;x) with integer coefficients, where m>=1,
the vector x consists of external natural parameters, and i is the index.
Let R_abs be the polynomial obtained by replacing each coefficient by its
absolute value.  If R=e-f is already given by two nonnegative-coefficient
polynomials, e+f can instead be used as the majorant, preserving DAG sharing.

For n>=1 and U>=0, define

    H = R_abs(n,U,...,U;x) + n + U + 1,
    s = 4 H!,
    m_i = s(i+1)-1       (0<=i<n),
    B = product_{i=0}^{n-1} m_i.

Write R(i,w;x)=sum_{a=0}^d R_a(w;x)i^a, where d is its degree in i; put
d=0 for the zero polynomial.  Define the explicit ordinary polynomial

    Rhat(s,w;x) = sum_{a=0}^d R_a(w;x)(1-s)^a s^(d-a).       (1)

Thus Rhat is the homogeneous substitution s^d R((1-s)/s,w;x), with all
denominators cleared in the displayed finite formula.  Formula (1), not an
expression involving rational evaluation at an unknown, is the definition.

For a fixed binary tree with k>=1 leaves, let N(z_1,...,z_k) be defined
recursively by N(z)=z and N(L,R)=N(L)^2+N(R)^2.  The same tree is used for
every evaluation.  A balanced tree minimizes its maximum degree in the leaf
symbols.  Binomial(A,k) means zero when 0<=A<k.

## 2. Homogeneous-index closure theorem

For each fixed n>=1, U>=0 and x in N, the following are equivalent:

1. For every i<n there exist w_1,...,w_m in {0,...,U} with R(i,w;x)=0.
2. There exist A_1,...,A_m in N such that

       B divides N(binom(A_1,U+1),...,binom(A_m,U+1),Rhat(s,A;x)).       (2)

There is no encoded index c in (2) and no index congruence leaf.  Since the
norm has m+1>=2 leaves it is nonnegative, so its divisibility can equivalently
be expressed by one natural quotient v and the equality N(...)=Bv.

### Proof of preliminary arithmetic

Each m_i is positive and congruent to 3 modulo 4.  Every prime divisor of m_i
exceeds H: a prime p<=H divides H! and therefore gives m_i=-1 modulo p.
The moduli are pairwise coprime.  Indeed, a prime divisor of both m_i and
m_j divides s(j-i); it cannot divide s, hence divides j-i, whose absolute
value is at most n-1<=H.  This contradicts the preceding property.

Every m_i has a prime divisor p_i congruent to 3 modulo 4.  Otherwise all
its prime factors congruent to 3 modulo 4 would have even multiplicity,
forcing m_i=1 modulo 4.  Fix any such p_i.  In F_{p_i}, -1 is nonsquare,
so a^2+b^2=0 implies a=b=0.  Induction on the fixed binary tree shows that
N(z)=0 modulo p_i if and only if every leaf vanishes modulo p_i.  A single
ordinary sum of three or more squares does not have this property.

### Soundness

Suppose (2).  Since p_i divides B, all the norm leaves vanish modulo p_i.
Because p_i>H>U+1, the factorial (U+1)! is invertible modulo p_i.  The
integer identity

    (U+1)! binom(A_j,U+1) = product_{r=0}^U (A_j-r)

therefore gives A_j=w_j modulo p_i for some w_j in {0,...,U}.  The same
prime p_i works for every coordinate j.  Its definition also gives

    s(i+1)=1 modulo p_i, and hence 1-s=s i modulo p_i.

Consequently the polynomial formula (1) implies

    Rhat(s,A;x) = s^d R(i,w;x) modulo p_i.

The integer s is a unit modulo p_i.  Thus the residual leaf gives
R(i,w;x)=0 modulo p_i.  Its absolute value is at most
R_abs(n,U,...,U;x)<H<p_i, so this congruence is an equality in Z.  This
provides a bounded witness for every i<n.

### Completeness

Suppose the first condition, and choose one bounded witness vector w_i for
each i<n.  Pairwise coprimality gives natural CRT representatives A_j with
A_j=w_{ij} modulo m_i for every i.  Every factor m_i is coprime to (U+1)!,
so the displayed falling-factorial identity implies binom(A_j,U+1)=0
modulo m_i.  Also s is a unit modulo m_i and s i=1-s modulo m_i.  Formula
(1), polynomial congruence, and R(i,w_i;x)=0 imply Rhat(s,A;x)=0 modulo
m_i.  Hence every norm leaf vanishes modulo every m_i.  Their pairwise
coprimality implies B divides the norm, as required.

All arguments use finite arithmetic, prime factorization and CRT, and are
formalizable in ZFC.  They do not assume any consistency or soundness axiom.
Existentially quantifying U removes the fixed witness bound, since there
are only finitely many indices.

## 3. An explicit special-function formula for B

As in the source-75 construction, no variable-length product has to remain
in the certificate language.  Put

    Q = (sn)^n+1,
    M = sQ+1,
    B = (s^n n! binom(Q+n,n)) mod M,                         (3)

where the remainder is the least nonnegative remainder.  The identity

    s^n n! binom(Q+n,n) = product_{j=1}^n s(Q+j)

and sQ=-1 modulo M show that the remainder equals the product of sj-1.
That positive product is strictly below (sn)^n<Q<M, so there is no wrap.
Formula (3) includes variable exponentiation and special functions; it
is not itself an ordinary polynomial definition.

## 4. Exact change from source 75

Source 75 uses the leaves

    binom(A_j,U+1) (1<=j<=m), R(c,A;x), s(c+1)-1,

where c is a separate CRT-packed index coordinate.  The new certificate
uses the first m leaves and the single homogeneous residual Rhat.  It
therefore eliminates c rather than merely dropping its necessary check.
The bound U, the m witness codes and the divisibility quotient are retained.
No new witness coordinate replaces c.

The old and new numbers of leaves are respectively m+2 and m+1.  A balanced
tree has maximal leaf degree 2^ceil(log2 k) for k leaves.  In particular,
when m=2^r-1 with r>=1, this formal leaf-degree bound falls from 2^(r+1)
to 2^r.  This is not an unconditional total-degree reduction of a fully
compiled polynomial: homogenization can increase polynomial degree in s,
and the graph implementations of binomial and factorial still matter.
The complete endpoint's variable and operation counts have not been measured.

The same mechanism applies whenever one has moduli m_i=s i+t with s a
unit modulo the selected prime divisors: replace the local index by -t/s
and homogenize.  For this particular arithmetic progression t=s-1.  It is
the prime divisor of the modulus itself that supplies the local index.

## 5. Why easier replacements fail

* Replacing the nested norm by an ordinary sum of three squares is invalid:
  1^2+1^2+1^2=0 modulo 3 without its three leaves being zero.
* A prime divisor congruent to 1 modulo 4 is insufficient for this binary
  norm: 1^2+2^2=0 modulo 5.
* The polynomial-value bound is necessary: a nonzero integer residual
  equal to p vanishes modulo p.
* The invertibility of s cannot be omitted from an abstract substitution
  lemma.  For R(i)=i and s=p, Rhat=1-p is nonzero modulo p whereas sR(0)
  vanishes.  The present m_i=s(i+1)-1 automatically makes s a unit.
* Dropping c without homogenizing would discard the connection between
  each index and the local equation.  Formula (1) is what preserves it.

## 6. Verification and provenance

`check_homogeneous_closure.py` is standard-library-only authored code and
contains no assert statements.  It runs identically under ordinary Python
and `python -O`.  The tests cover 1,125 exact rational substitution
identities; 650 modular index recoveries; 35 exact product, coprimality and
small-prime checks; 156,584 finite-field norm evaluations; and 896 complete
CRT certificates, including 79 successful certificates, 594 range
rejections and 223 residual rejections.  Four negative controls exercise
the mathematical restrictions.  These are diagnostic checks, not an
exhaustive substitute for the universal proof.

The inspected parent is ProveIt commit
`2605669a532342f153b13eb6b4a0af4b54f5fa37`.  The earlier mechanism and its
status statement are in:

https://github.com/VladimirReshetnikov/ProveIt/blob/2605669a532342f153b13eb6b4a0af4b54f5fa37/Computability/DiophantineConsistency/con-zfc-diophantine-forms/75-signed-bootstrap/certificates/INERT_PRIME_CLOSURE.md

The other direct-construction notes inspected were source 68's
`direct/COMMUTATIVE_CERTIFICATES.md`, source 73's
`research/junk_conservative_syntax.md`, and source 75's
`direct/BOUNDARY_THEOREM.md` and `REMAINING_FINITE_ARTIFACTS.md`.
They already address unordered Horn proofs, arithmetic syntax and
finite-input universal machines.  None supplies a newly instantiated
small ordinary Con(ZFC) polynomial independent of the established native
compiler.  The present theorem closes one local certificate optimization;
it does not complete those outstanding global compilations.
