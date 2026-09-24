# Use the binomial scale as the exponential witness: 103 operations

This is a simpler alternative to `PELL_SHARED_EXPONENT_PROOF.md`.
Start from the 104-operation certificate justified in
`PELL_SHARED_RATIO_PRODUCT_PROOF.md`. Keep its definitions

    N=n, R=r, U=wN^2, Y=sN^2,
    a0=Y(U+1), A=a0+4,
    D=UY, Q=UY^2, P=2Q+1,
    J=2R+1, K=k, C=c.

Keep its first Pell index equation `K=R+1+hD` and its shared norm
factorization. Change only the first exponential congruence, replacing
the target W=bw by the already calculated value W=U:

    d=U+C(A-4)+gamma(8A-17).                    (1)

All unknowns retain their positive integer domains. The defining
identity U=wN^2 is unchanged. This removes the separate multiplication
bw, giving 103 operations: 56 multiplications and 47 additions, with
34 positive unknowns and 22 equality tests. The independent coefficient
offset saving in `SINGLE_OFFSET_ENCODING_PROOF.md` composes with this
change; its complete checker is
`../verification/round22_1980_composed_certificate.py`.

## Sufficiency and the correct order of decoding

The unchanged coding bootstrap supplies

    N=q^8, q>4b>=8, 3L<=B<=N<=R, R<2N^3,
    U,Y>=N^2, N,R>=64.

The exact-index argument in `PELL_SHARED_RATIO_PRODUCT_PROOF.md` uses
none of the exponential congruences. It applies without modification:
the modulus D=UY satisfies D>=N^4>R+1, the interval gives C>J, and
the signed block and growth estimates prove

    C=psi_A(J), d=chi_A(J), K=psi_P(R+1).

With xi=(U+1)^(2R)/U^R, the same lower ratio estimate gives

    xi<C/K<Y+1,
    Y>=U^R, a0=Y(U+1)>U^(R+1), A>a0.           (2)

These conclusions precede either exponent equation. Since N>=64
and U>=N^2>=4096,

    4^(3J)=64*64^(2R)<=64*N^(2R)
           <=64*U^R<U^(R+1)<A,
    U^3<=U^R<A.

Equation (1) is exactly the source chi-congruence criterion for the
exponential relation with base 4 and target W=U. It therefore gives

    U=4^J.                                    (3)

Because U=wN^2 and all factors are positive integers, N^2 divides
the power of two U. Thus N is a power of two; so is q, since N=q^8.
No assertion that b is a power of two is made at this intermediate
stage, and none is needed to apply the second exponent criterion.

The positive gap, second main Pell norm and index congruence identify
kappa=psi_A(L), mu=chi_A(L), since 0<L<J<A. The unchanged bounds

    B^(3L)<=B^B<=N^N<=U^R<A,
    q^3<=N^N<=U^R<A

justify the second chi-congruence exponent criterion, which gives
q=B^L. Since q is a power of two and L is a positive integer, B is
a power of two. Finally B=Hb^2 implies that b is a power of two.
This restores exactly the binary radix conditions used in decoding.

The upper ratio estimate of `PELL_UNIT_SCALE_PROOF.md` is also
unchanged: U=wN^2 and R<2N^3 still justify its initial bound
8R/a0<16/N<1/2. Hence, after (2),

    0<C/K-xi<32R/(U+1).

By (3), U=4^(2R+1)>64R, so this error is less than 1/2.
Also U=4^J>4*2^(2R), giving the binomial expansion bounds

    0<xi-F<1/4,
    F=binom(2R,R) modulo U,

where F is the integer part of xi. Thus

    F<xi<C/K<Y+1,
    Y<C/K<xi+1/2<F+3/4.

Integrality forces Y=F. Since N^2 divides both Y and U by their
unchanged definitions, N^2 divides binom(2R,R). The binary no-carry
criterion and the established encoding proof now recover the
represented system. In this argument the old comparison U>=N*bw
is not used: the direct value U=4^J supplies both required error
bounds.

## Necessity and every changed positive witness

Start from a solution of the represented system and choose its
canonical coding witnesses as before. They determine b,B,q,N,R
before the Pell witnesses are chosen, with N a power of two,
R>=N, and N^2 dividing binom(2R,R). Set

    J=2R+1, U=4^J, w=U/N^2,
    Y=floor((U+1)^(2R)/U^R), s=Y/N^2,
    a0=Y(U+1), A=a0+4,
    Q=UY^2, P=2Q+1,
    C=psi_A(J), d=chi_A(J), K=psi_P(R+1).

The quotient w is positive integral. Indeed, N^2 and U are powers
of two and N^2<=R^2<=4^R<4^J=U. The binomial expansion, together
with N^2 dividing both U and binom(2R,R), makes s a positive integer.

At these chosen indices the same ratio estimates give

    Y<xi<C/K<xi+1/2<Y+3/4.

Consequently eta=C-KY and zeta=K-eta are positive integers.
Choose tau=(chi_P(R+1)-1)/2 and h=(K-R-1)/(UY).
The oddness of P makes tau positive integral. The congruence modulo
P-1=2UY^2 and strict Pell growth make h positive integral.

All remaining Pell witnesses are chosen by their generic constructions
at the new A, exactly as in `MAIN_PELL_BASE_FOUR_PROOF.md`: choose
positive f,i for the auxiliary norm; then use
G=1+(A+1)(f^2-1), I=chi_G(J), H17=psi_G(J),
o=(I+d)/f and j=(H17-J)/C. The signed-block proof establishes their
integrality and positivity. Choose kappa=psi_A(L), mu=chi_A(L),
Delta=(kappa-L)/(A-1), and phi=C-kappa; these are positive where
required because 2<=L<J.

The exponent congruences give integer gamma and rho. They are
positive because

    d-(A-4)C=4C-psi_A(J-1)>3C>U,
    mu-(A-B)kappa=B*kappa-psi_A(L-1)>(B-1)kappa>q.

Here A>U^3 and A>q^3 follow from (2) and the displayed exponent
bounds; C,kappa>=A since J,L>=2. Both moduli are positive. All
coding witnesses are preserved. This constructs a complete positive
solution of the new system. Its w and every dependent Pell coordinate
are re-chosen; the proof does not claim to preserve the previous
value w=4^J/b.

## Arithmetic and composition

The calculated register U=wN^2 already occurs in the first Pell norm
and in a0=UY+Y. Use that register directly in (1), deleting only the
old register bw. No new arithmetic or equality is introduced. The
first norm, its index modulus, and every other source polynomial
are unchanged; only E14 changes as a source equation.

The coefficient offset change affects only the coding block and
retains all pre-Pell inequalities used here. Conversely, the present
change retains every coding variable and equation. Their positive
necessity constructions occur in that order: choose the coding
witnesses, then choose U=4^J and the dependent Pell witnesses.
The two savings therefore compose to 102 operations, with
56 multiplications and 46 additions, 34 positive unknowns and 22
equality tests. The composed checker verifies its complete primitive
list and every source residual, including both triangular corrections.
