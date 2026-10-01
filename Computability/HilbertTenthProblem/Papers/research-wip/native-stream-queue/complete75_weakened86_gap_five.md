# Exact exclusion of gap five in the negative-index86 branch

The [gap-seven successor](complete75_weakened86_gap_seven.md) further
proves n<p<=2n-9 on R<0,mu>0, excluding96 power-of-two-X triples and all
three remaining small-X lanes. Larger odd gaps and mu<0 remain open;
this adds no universal86 claim.

Every positive zero of the [unchanged86 candidate](complete75_weakened_bound86_candidate.md)
with **R<0 and mu>0** must satisfy

    p odd, n<p<=2n-7.

The [gap-three theorem](complete75_weakened86_gap_three.md) had left
n<p<=2n-5. This note excludes p=2n-5. The crucial additional input is
the **exact main-root congruence**, rather than only its consequence
X<=2^p. It forces X=2^p under the gap-five hypothesis. The remaining
domain has only40 scale triples, and exact polynomial signs and integer
endpoints exclude both strict ratios at every allowed Y.

The [checker](complete75_weakened86_gap_five.py) and
[receipt](complete75_weakened86_gap_five.json) leave the candidate's
86=48M+38A source,19 positive coordinates and degree203 unchanged.
Larger odd gaps and mu<0 remain unresolved. This is not a universal86
bound or a counterexample to the full candidate; the established75/87
bounds are unchanged.

## 1. Necessary conditions at gap five

Assume a positive candidate zero with R<0, mu>0 and p=2n-5. The
[index-gap theorem](complete75_weakened86_index_gap.md) gives

    q=(B-1)J+1>=16, B=2^d, d>=4, J>=1,
    X=wq^3, Y=sq^3, w,s>=1,
    a=Y(X+1), A=a+2, H=4a+3,
    P=2XY^2+1, k=2*psi_P(n), c=psi_A(p),
    p odd, p>=13, n=(p+5)/2,
    kY<c<k(Y+1).

Write b_p=psi_2(p). Its wrap and growth estimates imply

    Y<=U=(2q^2-3)b_p+3p-1,
    (X+1)^((p-5)/2)<32Y^4(Y+1).                    (1)

Since b_p>=p, we have U+1<=2q^2*b_p. In particular(1) gives

    (X+1)^((p-5)/2)<1024q^10*b_p^5.                (2)

The actual computed main root is

    E_A(p)=chi_A(p)-(A-2)psi_A(p)=X+gamma*H.

As established in Section5 of the
[positive-index note](complete75_weakened86_positive_index.md),

    E_A(p)=2^p modulo H, 0<X<H,
    X=2^p modulo H, X<=2^p.                        (3)

This exact congruence is inherited before any Boolean typing of packed
fields. It follows, for example, from E_A(0)=1, E_A(1)=2 and its Pell
recurrence: modulo H, the sequence2^p obeys the same recurrence because
4-4A+1=-(4A-5)=-H. No input-root or first-index congruence is substituted
for the actual main-root equation.

## 2. The residue forces X=2^p

Suppose X<2^p. Congruence(3) makes 2^p-X a positive multiple of H,
so H<=2^p-X<2^p. Since H=4Y(X+1)+3,

    Y<2^(p-2)/(X+1).

Also Y>=4096, hence Y+1<2Y. Applying these bounds to(1) gives

    (X+1)^((p-5)/2)<64Y^5
                         <2^(5p-4)/(X+1)^5,

and therefore

    (X+1)^((p+5)/2)<2^(5p-4).                      (4)

But X>=q^3>=4096=2^12, so the left side of(4) is strictly larger
than 2^(6p+30), and 6p+30>5p-4. This is impossible. Together with
X<=2^p, it proves

    X=2^p.                                         (5)

This proof is uniform in all positive candidate coordinates. It does
not rely on testing finitely many main-root residues.

## 3. The complete finite domain

Because wq^3=2^p, unique prime factorization gives

    q=2^t, t>=4, 3t<=p, w=2^(p-3t).                (6)

No prior dyadic conclusion about q is assumed. Equation(6) is a
consequence of(5) and the retained positive integer scale w. Every q
listed below is compatible with at least the compiler representation
B=q,J=1; any other representation of that same q gives identical
necessary ratio tests.

The elementary recurrence for b_p gives b_p<=4^(p-1). From q^3<=2^p,
equation(2), and X=2^p, we obtain

    2^(p(p-5)/2)<1024q^10*b_p^5<=2^(40p/3).

All exponents can be cleared by cubing, with no numerical logarithm:

    3p(p-5)/2<40p, hence p<95/3.

Consequently the whole necessary domain is

    p in{13,15,17,19,21,23,25,27,29,31},
    q=2^t, 4<=t<=floor(p/3),
    X=2^p, w=2^(p-3t).                              (7)

There are exactly40 triples(q,p,w). For each, the positive scale
multiplier obeys

    Y=sq^3, 1<=s<=floor(U/q^3).                     (8)

The finite domain is an exact necessary superset; a row in it is not
claimed to satisfy the remaining candidate equations.

## 4. Exact monotone ratio certificates

Fix one triple in(7), and regard Y as a positive real variable. Define

    F(Y)=2Y*psi_(1+2XY^2)((p+5)/2)-psi_(2+(X+1)Y)(p),
    G(Y)=2(Y+1)*psi_(1+2XY^2)((p+5)/2)-psi_(2+(X+1)Y)(p).

The retained strict ratios require F(Y)<0<G(Y). Both polynomials have
degree p+4. Their coefficients are computed by the exact shifted Pell
recurrence used in the preceding gap-three checker. The new checker
verifies for both F and G, at every triple, that

    every coefficient below degree p is strictly negative;
    every coefficient of degree p or above is nonnegative;
    the leading coefficient is positive.                           (9)

Thus F(Y)/Y^p and G(Y)/Y^p are strictly increasing for Y>0: their
negative-power terms have negative coefficients and strictly increase,
and their nonnegative-power terms are nondecreasing. This proves that
each polynomial changes sign at most once, from negative to positive.
The80 per-triple sign certificates involve20 distinct coefficient
arrays, since X depends only on p.

For each triple, exact integer bisection locates the last multiplier
u in(8) with F(uq^3)<0, or u=0 if none exists. The checker then verifies:

* If u=0, F(q^3)>=0, excluding the lower ratio at every multiplier.
* Otherwise F(uq^3)<0, F((u+1)q^3)>=0 if u is below the upper bound,
  and G(uq^3)<=0. Monotonicity excludes the upper ratio at every
  multiplier at most u and the lower ratio at every larger multiplier.

All40 triples receive one of these certificates. Direct Pell recurrence
evaluation verifies the endpoints; a separate Horner evaluation of the
certified coefficient arrays agrees at every endpoint. Exhaustiveness
comes from the proved domain(7)--(8), the coefficient signs and the
endpoint inequalities, rather than from the bisection procedure itself.

Therefore p=2n-5 is impossible. The preceding theorem already made
2n-p an odd integer at least5. It is now at least7, proving the stated
conclusion n<p<=2n-7.

## 5. Why the exact residue matters

The weaker inequalities alone do not give the preceding finite cutoff.
For every odd p>=13, the family

    q=16, X=4096, n=(p+5)/2,
    Y=2^((3p-15)/2)

has X<=2^p, Y a positive multiple of q^3, Y<=U, and satisfies the coarse
growth inequality(1). At p=13 these assertions hold by direct integer
evaluation. Advancing p by2 multiplies Y by8. For q=16, U_p=509b_p+3p-1,
so b_(p+2)>13b_p and b_p>=p give

    U_(p+2)-8U_p>5*509*b_p-21p+13>0.

Thus the width comparison persists, including its linear term. The
same index advance multiplies the growth left side by4097, while the
right side multiplies by

    8^4*(8Y+1)/(Y+1)>4*8^4>4097.

Thus both comparisons persist indefinitely. Nevertheless H>2^p>X
throughout this family, so none satisfies the exact residue(3).
These are coarse-bound survivors only: neither the two strict ratios
nor complete candidate zeros are asserted. The checker audits251
members as a regression against dropping the exact congruence.

The checker also verifies396 exact main-root residue identities using
individual Pell roots. Those are separate component checks, not full
positive extensions. The universal exclusion is the proof in
Sections1--4 and its complete finite coefficient/endpoint certificate.
The branch mu<0 and gaps at least7 remain unresolved.

```sh
python3 complete75_weakened86_gap_five.py
```

Author receipt generation and a fresh default replay pass. All six local
links resolve. The root reviewer completed the full proof/source review
and a fresh default replay without findings. Its independent closed
Chebyshev binomial formulas generated all40 necessary triples, reproduced
all80 per-triple F/G coefficient arrays and their sign patterns, and
evaluated every recorded boundary without using the checker's Pell
recurrence. All independent checks passed.
