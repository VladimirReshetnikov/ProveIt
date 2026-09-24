# A doubled-index Pell congruence: 100 arithmetic operations

This note proves the positive-domain correctness of
`../verification/round24_1980_doubled_pell_certificate.py`, a change to
the 101-operation certificate of `FIXED_FOUR_ENCODING_PROOF.md`.
All fixed numerals are free. The new circuit has 56 multiplications
and 44 additions, with 34 positive unknowns and 22 equality tests.

The proof uses the same ordinary Pell classification, growth,
divisibility and chi step-down facts as `PELL_SIGNED_PROOF.md`.
It does not claim a newly compiled Lean theorem. All changed source
polynomials and their triangular corrections are checked separately
by the executable certificate.

## Definitions and the two changed equations

Use the main parameter and its norm coefficient

    A=a+4,       D=A^2-1,
    J=2r+1,     H_aux=J+j*c.

The supplied positive variable `a` retains its existing definition

    a=Y*(U+1),       U=w*n^2,       Y=s*n^2.

The first exponent equation still uses its computed modulus

    M=8*a+15=8*A-17,
    d=U+a*c+gamma*M.

Replace only the signed auxiliary norm E17 by

    v=o*f-d^2,
    K=D*(f^2-1),       G=2*K-1,
    v*(v+1)=K*(K-1)*H_aux^2.                  (1)

Here v, K and G are mathematical abbreviations, not additional
positive unknowns. The computed v may be negative. All original
unknowns, including o, remain positive.

The fixed-four coefficient code is still constructed with an
underlying power-of-two exponent L>=2. Replace the fixed index
component L by

    T_L=psi_4(L),

and replace E20 by

    kappa=T_L+Delta*a.                         (2)

Thus the supplied inputs are `(x,V,H,T_L)`, with the three
set-dependent components `(V,H,T_L)`. The constants V and H are
constructed from the same underlying L and compiled system as in
the fixed-four proof. No index component depends on x. The number
L is needed to define admissibility and prove decoding; it is not
an additional input to the final polynomial system.

All other source equations are unchanged.

## Sufficiency of the new signed auxiliary norm

At the point where the original signed block is used, the packing
and interval arguments have already established

    A>1,       1<J<c,       J odd.

They do not use the first exponential relation, E20, or the
coefficient decoding. The unchanged main and auxiliary norms

    d^2-D*c^2=1,
    f^2-D*(i*c^2)^2=1

give positive indices p and m such that

    d=chi_A(p),       c=psi_A(p),
    f=chi_A(m),       i*c^2=psi_A(m).

The standard divisibility fact used by the original signed proof
gives c|m from c^2|psi_A(m). Also p>=2: the case p=1 gives c=1,
contrary to c>J>1. The estimate

    psi_A(p)>=2p      for p>=2 and A>=2

follows from psi_A(2)=2A>=4 and, for p>=3, the growth bound
psi_A(p)>=(2A-1)^(p-1)>=3^(p-1)>=2p. Consequently

    0<2p<=c<=m.                              (3)

Since D>0 and f>1, K=D*(f^2-1)>1 and G=2K-1>1. Equation (1)
is precisely

    (2v+1)^2-(G^2-1)*H_aux^2=1.

The right side of (1) is positive, so v>=1 or v<=-2. Thus
I=|2v+1|>1. Pell classification supplies a positive index t with

    I=chi_G(t),       H_aux=psi_G(t).

Reduction modulo f gives the crucial doubled-index identities

    G=2D*(f^2-1)-1 = -chi_A(2)       (mod f),
    2v+1=2of-2d^2+1 = -chi_A(2p)   (mod f).

The identities chi_{-z}(t)=(-1)^t*chi_z(t) and
chi_{chi_A(2)}(t)=chi_A(2t) therefore imply

    chi_A(2t) = +/- chi_A(2p)        (mod chi_A(m)).

Apply the signed chi step-down lemma from the first section of
`PELL_SIGNED_PROOF.md`, with comparison index 2p and modulus
index m. Its hypothesis 0<2p<=m is exactly (3). It yields

    2t = +/-2p (mod 2m),
    t = +/-p   (mod m),
    t = +/-p   (mod c).                        (4)

No division modulo an even modulus is being assumed: an equality
2t=+/-2p+2mz is divided as an integer equality.

The unchanged auxiliary norm also gives c|f^2-1, so G=-1 modulo c.
The integer polynomial recurrence for psi gives

    psi_G(t)=psi_{-1}(t)=(-1)^(t-1)*t (mod c).

As H_aux=J+jc, (4) implies J=+/-p modulo c. Both J and p lie
strictly between zero and c. Hence J=p or J+p=c. The latter is
impossible: psi_A(p)=p modulo 2, while J is odd. Therefore

    p=J,       c=psi_A(J),       d=chi_A(J).    (5)

This proves exactly the main-index conclusion required by the
101-operation predecessor. Neither f nor v had to be assumed odd
or positive, respectively, in this sufficiency argument.

## Necessary positive witnesses for the new signed block

Suppose c=psi_A(J), d=chi_A(J), with A>1 and odd J>1. The auxiliary
witnesses f,i,j,o may be chosen again. Put

    m=2*c*J,
    f=chi_A(m),       i=psi_A(m)/c^2.

The quotient i is a positive integer. To see its divisibility
directly, expand

    (d+c*sqrt(D))^(2c).

The term contributing exactly one square root contains
(2c)*c=2c^2, and every remaining square-root term contains at
least c^3. Thus c^2|psi_A(2cJ). Moreover m is even, so
f=2*chi_A(m/2)^2-1 is odd. These choices satisfy E16.

Set K=D*(f^2-1), G=2K-1, and

    I=chi_G(J),       H_aux=psi_G(J).

The integer G is odd and exceeds one. Thus I is odd and greater
than one. Since J is odd, reduction modulo f gives

    I=-chi_A(2J)=1-2d^2 (mod f).

The positive integer I+2d^2-1 is divisible by f and by 2; because
f is odd it is divisible by 2f. Consequently

    v=(I-1)/2>0,
    o=(I+2d^2-1)/(2f)=(v+d^2)/f>0

are integers, and v=of-d^2. Also G=-1 modulo c and J is odd, so
H_aux=J modulo c. Strict Pell growth gives H_aux>J; hence

    j=(H_aux-J)/c>0

is an integer. The Pell norm for I,H_aux gives (1). This constructs
every changed signed-block witness with its required positive domain.

## Recovering the underlying fixed index without A-1

The preceding signed-block argument restores (5) before either
exponential decoding. All subsequent arguments through the first
exponent equation are unchanged from `PELL_COMMON_WITNESS_PROOF.md`.
In particular, the ratio lower bound first proves

    Y>=U^r,       a=Y*(U+1)>U^(r+1),

and the first exponent congruence then proves U=4^J. As r+1>3,
this gives the stronger bound for the actual modulus a:

    a>U^(r+1)>4^(3J).                         (6)

This assertion concerns a=A-4, not only A.

The unchanged second norm and gap c=kappa+phi supply a positive
index t_0<J with

    kappa=psi_A(t_0),       mu=chi_A(t_0).

Because A=a+4, the integer polynomial recurrence gives

    kappa=psi_4(t_0) (mod a).

Equation (2) therefore says psi_4(t_0)=psi_4(L) modulo a. The
fixed-four admissibility bounds still give 3L<=B<=n<=r, hence
L<J. For any 1<=s<J, the standard growth estimate and (6) give

    0<psi_4(s)<=8^(s-1)<4^(3J)<a.

Both residues are therefore in the interval (0,a), so they are
equal as integers. Strict growth of psi_4 gives t_0=L. The unchanged
second exponent congruence now proves q=B^L with exactly the same
size hypotheses as before. The binary radix, central-binomial
divisibility, and fixed-four coefficient decoding consequently follow
in the original proof order.

In necessity, set kappa=psi_A(L) and mu=chi_A(L), as before. Since
A=a+4, the quotient

    Delta=(psi_A(L)-psi_4(L))/a

is integral. It is strictly positive because A>4 and L>=2. For
example, the binomial expansion of the positive Pell solution
expresses psi_A(L) as a sum of positive terms increasing in A.
All other positive witnesses are supplied by the unchanged
common-witness construction, followed by the auxiliary construction
above. Thus the new fixed index and both changed equations preserve
existential representation in both directions.

## Complete arithmetic accounting and exact correction

Previously the norm coefficient required

    a_minus=a+3,       a_plus=a_minus+2,
    D=a_minus*a_plus.                         (3 instructions)

The new E20 needs neither affine parameter, and the new signed block
uses D itself. Since M=8a+15 is already required by E14, replace all
three instructions by

    a_square=a*a,       D=a_square+M.          (2 instructions)

The signed block retains its previous length. Its root register is
now v=of-d^2, using the already computed d^2. The old square and final
addition of one are replaced by v+1 and v*(v+1). Its three coefficient
instructions are K=D*AE, K_minus=K-1 and K*K_minus, where the existing
E16 register is AE=D*(ic^2)^2. Equation E20 still costs one
multiplication and one addition. The total saving is exactly one
addition: 101 becomes 100, with 56 multiplications and 44 additions.

For the nontrivial E17 substitution, write

    F16=f^2-AE-1,
    K_source=D*(f^2-1),       K_calc=D*AE.

Then K_source-K_calc=D*F16, and the checker verifies the exact
triangular identity

    F17_calc = F17_source
        +D*F16*(K_source+K_calc-1)*H_aux^2.

It also verifies the inherited E7 and E18 corrections from using
theta=B-4, every source residual, every serialized primitive addition
or multiplication, all input domains and arities, and the unchanged
fixed-four normal-form and support regressions. The universal support,
index and positive-domain claims are proved above and in the inherited
proofs rather than inferred from finite tests.
