# Independent order-filter audit and a seven-local gamma87 fixture

The [earlier compiler order filters](complete75_gamma87_compiler_order_filters.md)
already prove a two-state Lucas digit algorithm, prime-power order restrictions
strictly stronger than the coarse bounds below, actual compiler residue filters,
and proper-factor certificates. This packet independently implements the same
residue calculation with three states and audits a weaker size implication.
It adds an explicit modulo7 certificate at a main index satisfying the complete
kernel's range and population conditions. The algorithm and general exclusion
principle are not new results.

These are local number-theoretic filters, not a resolution of the candidate.
No actual compiled history, rejected-input full zero, or new universal bound
is supplied. The unchanged candidate costs87=47M+40A, has19 positive witnesses
and degree151. The separate proved75 certificate and normalized87 polynomial
of degree203 remain unchanged. The [checker](complete75_independent_gamma87_local_filters.py)
and [receipt](complete75_independent_gamma87_local_filters.json) preserve the
[unresolved candidate source](complete75_independent_gamma87_alias.md) and
record the exact finite evidence.

## 1. The fixed-history question and the locked main parameter

The [exact period criterion](complete75_independent_gamma87_period.md)
fixes a genuine compiled outer/main history at ordinary input x0. It has

    q=2^t>=16, R=3 mod4, 3q+1<=R<q^4,
    X=2^R, r=(R-1)/2,
    Y=(sum_(j=0)^r binom(2r,r+j)X^j)/2,
    a=Y(X+1), A=a+2, Delta=(a+1)(a+3), H=4a+3.       (1)

In particular a is even and divisible by3, Delta is odd and H is odd.
Let O=ord_H(2) and g=gcd(2Delta,O). On a history with its ordinary odd-power
marker W=2^(2d*x0+b), the exact history-preserving extension to another
positive input x exists if and only if

    alpha_old+2d*(x0-x)>0,
    g divides 2d*(x-x0).                             (2)

When these conditions hold, CRT gives arbitrarily large positive input
Pell indices and hence positive input delta,rho. The independent main
quotient stays fixed. This is a criterion for the specified history;
it does not classify all histories at a given input.

The recent all-input proof for the positive-complement candidate cannot
be transferred merely by freeing rho. Here the original positive F and
ordinary-input width are still retained. The complete main proof therefore
forces both equalities X=2^R and the unique half-binomial Y in(1), as proved
in [half-binomial42, Section5](pell_kernel_half_binomial42.md). H is fixed
once R is fixed. The other construction chose Y in an independent prime
progression in order to make H=3ell and control its period. That freedom
is absent here. Varying R across actual compiled histories is a further
problem; this observation does not prove that any useful factorization
of H is impossible.

## 2. An independently audited coarse upper restriction

For even a,

    gcd(a+1,a+3)=1, gcd(Delta,H) divides9.             (3)

Indeed H=4(a+1)-1 and H=4(a+3)-9. Thus the first factor has gcd1 with H,
and the second has gcd dividing9.

Let p>=5 be prime, let k>=1, and suppose w=p^k divides Delta. Exactly one
of a+1 and a+3 is divisible by w. If w also divides O, then

    w|a+1:       H >= (w+1)(w-1),
    w|a+3:       H >= (w+1)(w-9).                    (4)

To prove this, factor H abstractly as a product of powers of distinct
primes ell. The order O divides the least common multiple of
ell^(e_ell-1)(ell-1), by the Chinese remainder theorem and Fermat's theorem
(or the unit-group order at each prime power). By(3), p does not divide H.
Consequently a factor ell^(e_ell-1) cannot supply p. The full p^k component
of that least common multiple must come from ell-1 for at least one prime
ell dividing H. In particular

    ell=1 mod w, ell>=w+1.                            (5)

Set c=H/ell. Since ell=1 modulo w, we have c=H modulo w. In the first
case H=-1 modulo w, so the positive c is at least w-1. In the second
H=-9 modulo w, so c>=w-9. The latter inequality is harmless when w<=9,
and is its least-positive-residue bound when w>9. Multiplying these lower
bounds with(5) proves(4).

Equivalently, every shared component w satisfies the integer caps

    w|a+1:       w <= floor(sqrt(H+1)),
    w|a+3:       w <= 4+floor(sqrt(H+25)).             (6)

The second follows from (w-4)^2<=H+25. Thus any known p^k dividing Delta
and exceeding its cap is excluded from the order, and hence from g.
No factorization of H and no computation of O is needed to use that exclusion.
The proof uses a prime divisor only to establish the implication.

For genuine main data, a is also divisible3. The earlier packet's Section5
uses this and oddness to prove the following strictly stronger necessary
inequalities for the same shared component w:

| w modulo3 | w divides a+1 | w divides a+3 |
|---|---|---|
|1|H >= (4w+1)(4w-1)|H >= (4w+1)(6w-9)|
|2|H >= (2w+1)(2w-1)|H >= (2w+1)(6w-9)|

It bounds both the prime ell and the cofactor H/ell using parity and their
residues modulo3. Its table should be used for exclusions on genuine main
data; (4)--(6) are retained here only as a simpler independently audited
consequence, not as an improvement.

This restriction controls individual prime powers, not their product.
It does not bound g by q or guarantee any alias within the positive width
in(2). It also deliberately excludes p=3, which can divide H itself.
The prior packet's local3 analysis remains applicable; other factors of H
can contribute further powers of3 to O, as that packet already explains.

## 3. An independent three-state version of the known digit algorithm

The residue formula and Lucas digit method are already proved in the earlier
packet's Section3. The following proof documents this separate implementation;
keeping the less-than state is redundant mathematically but allows a direct
three-way comparison invariant.

For an odd prime p and integer R>=3 odd, let r=(R-1)/2 and X=2^R modulo p.
This X is nonzero. Define the upper binomial tail

    T_p(r,X)=sum_(k=r)^(2r) binom(2r,k)X^k mod p.

Then the exact value of(1) modulo p is

    a=(X+1)*2^(-1)*X^(-r)*T_p(r,X) mod p.           (7)

Both inverses exist. This evaluation does not claim that the corresponding
X,Y,H have been constructed as integers.

Write n=2r, n=sum n_i p^i and k=sum k_i p^i. Over the field with p elements,
(1+z)^(p^i)=1+z^(p^i). Multiplying these identities according to the digits
of n gives the Lucas formula

    binom(n,k)=product_i binom(n_i,k_i) mod p,

where a factor is zero when k_i>n_i. Also X^(p^i)=X, so X^k is the product
of X^(k_i). It therefore suffices to sum over k_i in[0,n_i], retaining
only integers k>=r.

Process the digits from most significant to least, padding r with leading
zeros to the same length as n. Maintain three weighted sums whose states
say that the chosen prefix of k is less than, equal to, or greater than
the corresponding prefix of r. For each digit k_i, multiply its incoming
weight by binom(n_i,k_i)X^(k_i). A non-equal relation persists; an equal
relation changes according to k_i compared with the digit of r. At the
end add the equal and greater states. This is exactly T_p, because every
nonzero Lucas term has one digit path and the three states implement the
ordinary integer comparison k>=r. Terms with zero Lucas coefficient may
be omitted even when their ordinary binomial coefficient is nonzero.

After an O(p^2) precomputation of the binomial table modulo p, there are
at most three states and p transitions per state per digit. Successive
multiplication computes the p digit weights in O(p) field operations.
The tail calculation uses O(p(1+log_p R)) field operations and O(p^2) table space,
plus modular exponentiations in(7). For any fixed small prime this depends
on the number of digits of R, rather than on the bit length of Y or H,
which is quadratic in the numerical index R. Primality of the supplied
modulus is required; the implementation checks it exactly by trial division.
This is not a composite-modulus or prime-power Lucas algorithm.

## 4. A seven-local obstruction at genuine kernel parameters

Take

    R=753407, q=32, t=5, r=376703.                  (8)

These satisfy R=3 modulo4, 3q+1<=R<q^4 and popcount(R)=17=3t+2.
Thus the full half-binomial kernel theorem applies with D0=q^3: its
canonical X,Y are positive multiples of q^3, both strict ratios and the
main/first equations have their positive solution, and the complete
strong auxiliary extension is available. The large integers themselves
are not materialized here.

The exact algorithm(7) gives

    a=6 mod7, a=31 mod127.                           (9)

Consequently 7 divides a+1 and hence Delta, while127 divides H=4a+3.
The integers7 and127 are prime, 2^7=1 modulo127, and2 is not1 there;
therefore ord_127(2)=7. Since127 divides H, its order divides O. Hence

    7 divides gcd(2Delta,O)=g.                       (10)

Whenever an actual compiled history has the two parameter residues in(9),
its history-preserving input aliases must satisfy

    7 divides d*(x-x0).

For actual modified compiler widths d=5^s, this is exactly x=x0 modulo7.
The prior packet already gives proper-factor obstructions beyond its local
power-of-three test, including a packed fixture forcing input differences
divisible51. Its saved examples and48 packing audits have discriminant/order
prime hits3,5,17, but none certifies7; factor5 does not restrict inputs when
d is a power of5. Thus (8)--(10) add a distinct local7 fixture, not a stronger
general filter or a stronger overall history contract. The prior two-state
evaluator independently agrees with both residues in(9).

As the prior packet proves more generally, any certified small prime ell
dividing H, with p dividing its
exact order and p dividing Delta, gives an analogous necessary p-local
condition. Formula(7) can check the two residues without constructing H.

The fixture(8) supplies genuine main-kernel numerical prerequisites, not a
complete compiler history. In particular its masks, transport and program
recipe are not instantiated. It is not a full candidate zero and is not
an actual rejected-input example. The conditional statement for actual
histories follows from(9)--(10), regardless of whether this particular R
occurs in an actual compilation.

## 5. Evidence and remaining target

The source is unchanged, and its hash and private rho/sigma consumers are
audited. The checker compares the digit algorithm with direct exact binomial
sums on896 prime/index pairs, and checks20 large-index tail-reciprocity
identities at indices up to1025 bits. At(8), a separate enumeration of all
upper-half Lucas terms verifies both residues in(9), using753,408 terms
and no prefix-state dynamic program.

Six hundred small even arithmetic hosts compute their full power-of-two
orders directly. Every prime-power factor p^k of Delta with p>=5 is checked
against(4)--(6); when it occurs in the order, an explicit prime divisor ell
with ell=1 modulo p^k is independently found. These small hosts check the
uniform number-theoretic implication and are not called compiled histories.
The receipt reports the exact component and exclusion counts.

The next accepted-language task is still to find an actual compiled parent
history and a rejected x satisfying the full criterion(2), or to prove a
history-normalization or exclusion theorem that settles all such transfers.
The existing filters can rule prime-power components out of g or certify local
divisors that every alias must respect. They do not replace the full order
criterion, turn a finite test into a full positive zero, or supply a uniform
small bound on g. Author receipt generation and fresh default replays pass.
Independent full proof/source/dependency review and fresh replay pass after
the digit-weight implementation and complexity bound were aligned. A separate
least-significant-digit threshold recurrence checks512 generic tails against
exact binomials,604 values of a covering both odd index classes,32 large-index
cases through1025 bits, and both fixture residues. An independent order oracle
checks1000 even hosts and3197 prime-power components, including208 explicit
shared-order prime witnesses and1391 cap exclusions. Local links and
whitespace checks pass. A second full proof/source read also passes. These
reviews retain the main-kernel-only scope: no compiled history or complete
candidate zero is supplied by the fixture.

A final provenance review and fresh replay also pass after explicitly crediting
the earlier algorithm and stronger bounds. It confirms that the saved earlier
receipt has prime hits3,5,17, no7, and no matching fixed index or packing hash.
The earlier public `factor_certificate(753407,(127,))` independently returns
the squarefree divisor14 and ordinary-input divisor7. All six local links
resolve. This confirms the additional fixture while leaving the general
method and theorem attributed to the earlier packet.
