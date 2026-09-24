# One operation saved with the alternate Pell parameter

This note accompanies
`../verification/round4_1980_pell_optimized_certificate.py` and its
119-operation certificate. It builds on the preserved 120-operation
packed certificate and changes only the Pell parameter inside E17.

## The source explicitly permits the alternative

The corrected 1982 source, Lemma 2.28 and its following remark, treats
`C=psi_A(B)` under the hypotheses

    1<A, 1<B<=C, and either 2B<=C or B odd.

Its equations P1--P7 include

    F | I-D,
    D^2=(A^2-1)C^2+1,
    E=i C^2,
    F^2=(A^2-1)E^2+1,
    G=A+F^2(D^2-A),
    H=B+j C,
    I^2=(G^2-1)H^2+1.

The following remark states explicitly:

> Of course (P5) may be replaced by G=A+F^2(F^2-A).

Corollary 2.29 eliminates E,H,I by substitution, writing I=D+oF.
The same substitution applies to this explicitly permitted alternative.
In the present variables we use A=a, B=2r+1, C=c, D=d, F=f. Thus the
alternative E17 is

    (d+of)^2 = ((a+f^2(f^2-a))^2-1)(2r+1+jc)^2+1.

## Hypotheses and positive witnesses

The packed system already proves n>=2 before invoking the Pell lemmas.
Put Y=sn^2. E8 and E11 give p>=2 and k>=r+2, while E10 gives

    |c-kY| < k/2.

Since Y>=4, it follows that

    c > (Y-1/2)k >= (7/2)(r+2) > 2r+1.

E12 gives a=(wn^2+1)rY>=20r>1. Thus the source hypotheses hold:
a>1, 1<2r+1<c, and 2r+1 is odd. These deductions are independent
of E17 and of which of its two parameters is used.

The positive quotient o remains available by an explicit construction;
we do not assume that the integer I occurring in the source lemma is
already positive. Suppose c=psi_a(J), where J=2r+1, so that
d=chi_a(J). Keep any positive f,i satisfying E16. Then

    f^2=(a^2-1)i^2c^4+1 >= (a^2-1)c^2+1=d^2,
    f^2>=a^2.

Hence the alternate G=a+f^2(f^2-a) satisfies G>=2a+1. Moreover
G is congruent to a modulo f, and G is congruent to 1 modulo c,
since f^2 is congruent to 1 modulo c. Define

    I=chi_G(J), H=psi_G(J).

The Pell coordinates at a fixed index are polynomials with integer
coefficients in their base. Thus

    I = chi_G(J) = chi_a(J) = d (mod f),
    H = psi_G(J) = psi_1(J) = J (mod c).

Here psi_1(J)=J denotes evaluation of the same recurrence polynomial
at 1. Strict growth gives I>chi_a(J)=d and H>J, since G>=2a+1
and J>1. Therefore

    o=(I-d)/f >=1, j=(H-J)/c >=1.

The Pell identity for base G verifies the alternative E17. Conversely
any positive o in that equation supplies I=d+of and satisfies P1.
This is also the explicit construction in the checked-in Lean theorem
`exists_PConds` in `Lean/Diophantine/Paper1982/Psi.lean`, with its
Boolean argument `false`; the argument above does not rely merely
on the existence of an unsigned square root in the printed lemma.

Consequently either version of E15--E17 is equivalent, under these
already proved hypotheses, to c=psi_a(2r+1). The remaining equations
do not involve j,o, so these may be re-chosen when passing between
the two systems. The same construction also applies to the original
G=a+f^2(d^2-a): it has G>=2a+1, G=a modulo f, and G=1 modulo c.
Thus f,i can in fact be preserved. The coordinate d is preserved: it is the unique
positive square root of (a^2-1)c^2+1. This is existential equivalence
with re-choice of the four indicated witnesses, not a claim that the
same f,i,j,o satisfy both versions of E17.

## Four operations in place of five

Write F2=f^2, A=a^2-1, and X=A(ic^2)^2. The E16 computation already
produces X, with E16 asserting F2=X+1. The value a-1 is already
needed by E20; move its existing instruction before the E17 block.
For the alternate parameter G=a+F2(F2-a),

    G-1 = (F2-1)(F2-a+1).

The replacement block is therefore

    J = F2-(a-1),
    Gminus1 = X J,
    Gplus1 = Gminus1+2,
    G2minus1 = Gminus1 Gplus1.

These four operations replace the previous five computing
d^2-a, f^2(d^2-a), G, G^2, and G^2-1. The full certificate has
119 operations: 68 multiplications and 51 additions, with subtraction
represented by an addition as in the original definition.

## Exact triangular verification

The program does not assert that X=f^2-1 is a polynomial identity.
Let F16=f^2-X-1, J=f^2-a+1,

    G_source=a+f^2(f^2-a),
    G_calculated=1+X J,
    H=2r+1+jc.

It verifies exactly that

    F17_calculated = F17_alternate
                    + F16 J (G_source+G_calculated) H^2.

Thus E16 being zero makes the new comparison equivalent to the
alternate E17. The other triangular identity is the previously
verified E7 correction using E2 and E3. Every remaining comparison
is checked as an exact source residual, and every serialized
addition or multiplication is checked independently.
