# Compiler and factor filters for the independent-gamma87 period

The actual fixed compiler restricts the ternary obstruction from the
[exact input-period criterion](complete75_independent_gamma87_period.md).
The parity of its window-selector count and tile alphabet already rules
that obstruction out for whole classes of genuine histories. A separate
digit algorithm computes the half-binomial parameter modulo a small odd
prime without constructing its enormous integer value. This supplies
certified factors of the period gcd, including contributions invisible
to the local power-of-three calculation. An elementary complementary
bound excludes sufficiently large prime-power contributions.

These are filters for the unresolved87 candidate, not a new universal
equation or a complete false-input construction. The established bounds
remain a75-operation certificate and an88-operation polynomial. The
[source](complete75_gamma87_compiler_order_filters.py) and
[receipt](complete75_gamma87_compiler_order_filters.json) leave every
parent arithmetic schedule unchanged.

## 1. The parameter and the actual compiler's fixed residues

Use a for the main Pell parameter, R for its genuine main index, and
r0=(R-1)/2. The restored main kernel gives

    X=2^R, Y=(sum_(j=0)^r0 binom(2r0,r0+j) X^j)/2,
    a=Y(X+1), Delta=(a+1)(a+3), H=4a+3,
    R=3 mod4, q=2^t>=16, Y=s*q^3.

In particular a is even and divisible3. The exact fixed-history input
criterion uses O=ord_H(2), g=gcd(2Delta,O): for a parent history at x0,
an ordinary input x can use those same outer/main data exactly when

    alpha_old+2d*(x0-x)>0 and g divides 2d*(x-x0).       (1)

The cited packet proves both directions and the positive extension. This
packet narrows the divisibility part; it does not remove the width test.

Now inspect the **actual** sparse layout in
[the modified75 compiler](complete75_half_binomial_compiler.md#1-fixed-layout-and-modified-masks).
Let k be its number of window selectors and a_T its tile-alphabet size.
Let m be the layout's even clause/copy count. The radix is 2^b, the cell
base is B=2^d, and b,L,d=bL are odd powers of5. Hence both radix and B
are -1 modulo3. No huge fixed numeral needs to be materialized to take
these residues.

The payload exponents form the interval from k+3a_T through k+12a_T-1.
The dummy interval starts at k+12a_T and ends at m+3a_T-4. Therefore
the anchor unit is

    M=m+6a_T-3,

which is odd, and all four anchors M,3M,9M,27M are odd. The added free
dummy bit is at the first dummy exponent k+12a_T, of parity k.

The two center-clause bands of MF0 cancel modulo3: their separation
2Emax+1 is odd. Each of the two copy-test families has zero alternating
sum. If a_T is odd, its two adjacent row/column groups cancel; if a_T
is even, its sum over symbol positions cancels. The two remaining
anchor tests each contribute -1. Thus MF0=-2 modulo3. The modification
MF=MF0+4 proves

    MF=2 mod3.                                         (2)

For MC, evaluate its actual formula

    MC=B-1-sum_(e in E,e!=1) (2^b)^e-2(2^b)^(k+12a_T).

Put epsilon=(-1)^k. The selector alternating sum is 1 for odd k and0
for even k. The payload sum is0 for even a_T and -epsilon for odd a_T.
The dummy sum is epsilon when k+a_T is even and0 otherwise. The four
anchors sum to -4; deleting exponent1 from this total adds1. Substitution
gives the exact residue table

| Window selectors k | Tile alphabet a_T | MC modulo3 |
| --- | --- | ---: |
| Odd | Either parity | 2 |
| Even | Even | 1 |
| Even | Odd | 0 |

These are identities of the real layout, not experimental properties of
toy masks. The optional high DC correction does not enter either mask.
The table uses the current effective exporter, which chooses the first
dummy for the extra free bit. Choosing a different dummy is a different
fixed layout and requires recomputing its MC residue.

## 2. Consequences for every packed history of that compiler

With q=B^N and J=(q-1)/(B-1), the actual source uses

    R=(q^2-Z-qF)(q^2-1)+(MC+q*(MF+B-1))J.              (3)

In particular J divides R. Retaining the source's MF+B-1 offset is
essential in the following residue calculation. Since B=-1 modulo3,

    N even: q=1, J=0, R=0 mod3;
    N odd:  q=-1, J=1, R=MC-MF-1=MC mod3.             (4)

Thus the table in Section1 determines R modulo3 for every odd-length
history, independently of its data, convolution values, and dummy
choices. Every canonical completeness history has N a power of5 and
hence is in this odd case. Equation (4) also covers noncanonical even N.

The preceding period packet proved

    a=6 mod9 iff r0=0 mod3 and every ternary digit of r0 is0 or1;
    otherwise a=0 mod9.                               (5)

The first alternative requires R=1 modulo3. Combining (4)-(5), it can
occur only when **N is odd, k is even, and a_T is even**. For every other
case, all genuine histories have a=0 modulo9. Their local power-of-three
obstruction exponent h=min(v3(Delta),v3(H)-1) is therefore zero.
In the remaining case the no-ternary-digit2 test is still required.

This does not show that3 fails to divide the full g. Orders at other
prime factors of H can contribute3, as Section4 demonstrates. Also the
actual d is a positive power of5, so3 never divides d: whenever the full
g does contain3, (1) really restricts ordinary inputs modulo3.

## 3. Computing a modulo a prime without constructing Y or H

Fix an odd prime p. Put n=R-1=2r0 and x_p=2^R modulo p. Then

    a=(1+x_p)/(2*x_p^r0)
         *sum_(k=r0)^n binom(n,k) x_p^k mod p.           (6)

The denominators are invertible. This formula remains valid when
x_p=-1; it then returns a=0 without dividing by 1+x_p.

Write n and r0 in base p. From
(1+z)^p=1+z^p in the prime field, the coefficient identity is

    binom(n,k)=product_i binom(n_i,k_i) mod p.

Also x_p^(p^i)=x_p. The weighted sum in (6) can therefore be evaluated
by a digit comparison with r0, processing the most significant digit
first. Maintain two weights: prefixes equal to the threshold and prefixes
already greater. At a digit with n_i=N_i and threshold digit r_i, form

    w_j=binom(N_i,j)*x_p^j, 0<=j<=N_i,
    total=sum_j w_j, above=sum_(j>r_i) w_j,
    exact=w_(r_i), or0 when r_i>N_i.

The updates are

    greater_new=greater*total+equal*above,
    equal_new=equal*exact.

Their final sum is exactly the upper tail, including the central term.
No symmetry approximation or carry omission is used.

Factorial and inverse-factorial tables up to p-1 cost O(p) prime-field
work; each digit costs O(p). Including modular powers gives
O(p log R) field operations, and O(log R) for each fixed p. These are
algorithmic field-operation estimates, not bit-complexity bounds or a
low-cost Diophantine certificate. The algorithm is given the integer R
in binary and extracts its base-p digits. It does not claim to evaluate
an unspecified exponentially compressed R for free.

## 4. Certified lower divisors of the full period gcd

Suppose an odd prime ell satisfies 4*a_mod_ell+3=0 modulo ell, as
verified by (6). Then ell divides the genuine H. Let e_ell be the
verified order of2 modulo ell. For every odd prime p dividing e_ell,
another application of (6) tests whether

    (a_mod_p+1)(a_mod_p+3)=0 mod p.

If so, p divides both Delta and O, hence p divides g. The order
certificate consists of 2^e_ell=1 and 2^(e_ell/p)!=1 for every prime
p dividing e_ell. Together with the always-present factor2, products
of distinct certified primes form a squarefree divisor L of g.

Thus L/gcd(L,2d) divides every allowed input difference in (1).
For the actual five-power d and squarefree L this divisor is
L/gcd(L,10). A certified factor5 alone does not distinguish ordinary
inputs in this compiler; factors3,7,11,17 and so on do.

Two exact examples illustrate what this filter can detect. They are
**mask-packing fixtures, not compiled histories**:

* B=64,N=1,MC=62,MF=4,Z=1,F=20 gives R=11531775.
  It satisfies the mask contract, packed range and exact population20.
  R is divisible3, so a is divisible9 and the local exponent h is0.
  Nevertheless the digit algorithm gives a=1 modulo7; hence7|H and
  ord_7(2)=3, certifying6|g.
* B=32,N=3,MC=26,MF=12,Z=1061,F=17936 gives
  R=521853468584832895, of population47=3*15+2. The two no-carry mask
  tests and the packed range hold. The residues are a=25 modulo103
  and a=14 modulo17. Since ord_103(2)=51, these certify102|g. If these
  data belonged to an actual compiler history with five-power d, its
  fixed-history input aliases would have differences divisible51.

No C, alpha, marker, transport quotient or computation is supplied for
these fixtures. The first also has d=6, outside the actual layout's
five-power choice. Neither is evidence of a rejected input admitted by
the full source. Their role is to verify proper-factor certificates on
large exact packed indices without constructing X, Y or H.

## 5. Large prime-power factors which cannot contribute

There is a complementary upper filter which needs no factorization of H.
Let p>=5 be prime and m=p^e divide g. Since a is even, a+1 and a+3
are coprime, so m divides exactly one of them. Moreover

    gcd(H,Delta)=gcd(H,9),

as follows from 16Delta=(H+1)(H+9). Hence p does not divide H.

The order modulo H is the least common multiple of the orders modulo
its prime powers. The order modulo ell^f divides ell^(f-1)(ell-1).
Because p does not divide H, some prime ell dividing H must therefore
satisfy ell=1 modulo m. This is an implication only; it does not assume
that all of ell-1 occurs in the order of2.

Write H=ell*n. Both ell and n are odd. The prime ell is not3, since
p divides ell-1; thus n is a multiple of3. If m divides a+c, with
c=1 or3, then H=-(4c-3) modulo m and consequently

    n=-(4c-3) mod m.

These parity and modulo3 restrictions give the following exact lower
bounds, necessary for m to contribute to g:

| m modulo3 | If m divides a+1 | If m divides a+3 |
| --- | --- | --- |
| 1 | H >= (4m+1)(4m-1) | H >= (4m+1)(6m-9) |
| 2 | H >= (2m+1)(2m-1) | H >= (2m+1)(6m-9) |

Indeed ell=k*m+1 requires positive even k. If m=1 modulo3, k=2
would make ell divisible3, so k>=4; if m=2 modulo3, k>=2 suffices.
For c=1, n=j*m-1 is odd and divisible3, forcing j>=4 or j>=2 in
the two rows. For c=3, n=j*m-9 forces j to be a positive even
multiple of3, hence j>=6. Since m>=5, all displayed bounds are positive.

Violation of the appropriate bound proves that m does not divide g.
It is not necessary to compute O or find the witnessing prime ell.
The bounds do not give a small uniform bound on the product g: many
smaller prime-power contributions may remain. They therefore do not
by themselves prove or exclude an ordinary-input alias.

## 6. Evidence and the next unresolved step

The checker compares the digit algorithm with400 fully materialized
integer half-binomial residues and256 independent direct modular tails.
It audits35 actual sparse compiler layouts without materializing their
fixed masks, and432 exact numerical instances of the packed residue
identity, including the MF+B-1 source offset.

There are48 further exact packed-mask fixtures, up to10,240 bits in R,
with deterministic proper-factor certificates. They do not assert a
universal numerical alphabet or a genuine computation. The complementary
large-prime-power implications are checked on854 admissible factor pairs;
no completed whole-period sweep from the preceding packet is repeated.

Normal execution checks the saved receipt; --write-receipt regenerates
it. The new results separate three issues: restrictions imposed by the
actual compiler, local orders detectable without huge Pell integers,
and prime-power order contributions which are impossible by size. A
complete alias construction still needs an actual parent history, its
positive width at a rejected input, and the full compatibility condition
(1). No such construction is claimed here.

Independent proof/source review and fresh default receipt replay passed.
A separate implementation checked4,608 modular Pascal tails,167 prime
orders and399 contributing prime-power cases from exact orders for
2,000 parameters a=6,12,...,12000. The root proof/source review and
default replay also passed. These finite checks support the parametric
arguments above; none constructs a complete false-input witness.
