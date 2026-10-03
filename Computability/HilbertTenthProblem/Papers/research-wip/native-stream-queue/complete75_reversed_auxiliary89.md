# Reversing the auxiliary unit gives 89 operations at degree160

The fixed complete75 compiler admits a single polynomial of **89=48M+41A
operations**, exact degree **160**, and **19 strictly positive existential
witnesses**. This retains the ordinary positive input x and all fixed program
numerals of [norm product89](complete75_norm_product89.md), whose degree is166.
The comparison certificate still costs88=48M+40A and has one equation; the
best complete comparison bound remains75.

Three literal gate changes suffice. Evaluate the auxiliary norm at `of-c`,
reverse the sign of the linear-unit residual, and use the already computed
strong-auxiliary right side as the norm multiplier. The strong unit restores
the original square multiplier before the negative-Pell exclusion is used.
The reversed linear sign makes each additional unit branch incompatible with
the first/main Pell ratio. Both directions preserve all nineteen coordinates.

## 1. The polynomial and its domain

Keep exactly the definitions, fixed compiler numerals, and nineteen positive
coordinates of [89, Section1](complete75_norm_product89.md). In particular

    q=(B-1)J+1, X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, a=E+Y, c=kY+eta,
    A=a+2, Delta=A^2-1,
    C=q-F-Z-alpha-2d*x,
    R=(q^2-Z-qF)*(q^2-1)+(MC+q*(MF+B-1))*J,
    T=i*c^2, U=jc-R, V=of-c, K=Delta*(f^2-1).          (1)

The fixed constants satisfy B>=16, d,b positive, 0<MC,MF<B-1, and
K0=DC+B*DR>0. The literal source uses Jrep for J and y_aux for y.
As in89, A is a proof abbreviation while register `A` stores Delta.
All definitions are computed registers, not extra supplied witnesses.

Keep the five factors N0,N1,N2,Nk,Nt from89, and the strong factor N4:

    N0=tau^2-(E^2+X)(kY)^2,
    N1=D^2-Delta*c^2,
    N2=mu^2-Delta*kappa^2,
    Nk=k-R-hE,
    Nt=(K0+X)C+(q-F)-zplus*(q-1),
    N4=1+T^2-K.                                       (2)

Here D,kappa,mu retain their literal89 definitions. Replace the auxiliary
and linear factors by

    M3=K*(V^2-y^2)+y^2,
    L=1+V-U.                                         (3)

The output polynomial is

    P=N0*N1*N2*M3*Nk*Nt*N4*L-1.                       (4)

Its integer zero set is considered only for positive x and all nineteen
positive supplied coordinates. Computed values such as C,R,mu,U,V may be
signed off that zero set. No positivity test of an intermediate is added.

## 2. Unit signs and the strong square

At an integer zero of(4), every factor is1 or-1. The negative-Pell exclusions
from89 immediately give N0=N1=N2=1, allowing signed mu. Its separate modulo4
lemma gives **N4=1** for any integer A,T,f: N4=-1 would require

    T^2+2=(A^2-1)(f^2-1),

which forces T^2=2 or3 modulo4. Consequently

    K=T^2.                                           (5)

Only now rewrite M3 as

    M3=(TV)^2-(T^2-1)y^2.

Since T=ic^2>=9, the negative-Pell lemma for parameter T excludes M3=-1,
regardless of the sign of V. Thus

    N0=N1=N2=M3=N4=1,
    Nk,Nt,L in {1,-1}, Nk*Nt*L=1.                     (6)

There is also a direct unconditional exclusion: for any integer A,f,
`K=(A^2-1)(f^2-1)` is0 or1 modulo4. In those two cases M3 is respectively
y^2 or V^2 modulo4, and therefore cannot be-1. Our proof above uses(5)
to restore the familiar norm; the square identity remains essential for
the later ordinary Pell classification. This is the same multiplier substitution
used in the separate [strong reduction89](complete75_strong_reduction89.md)
construction; the present polynomial additionally changes the root and sign.

## 3. Bounds valid for both index and linear signs

Put Nk=epsilon_k and L=lambda, with epsilon_k,lambda in{1,-1}. The weak-transport
bootstrap from89 uses only Nt in{1,-1}:

    (K0+X)C=F+(zplus-1)(q-1)+(Nt-1)>=-1.

As K0+X>1, integrality forces C>=0, and the positive input and slack imply
F+Z<q. Exactly the packing estimates from90/89 give

    (2q-1)(q^2-1)<R<q^4-q^3<q^4, R>3q+1,
    E>=q^6>2(R+2), a>R.                               (7)

For the strengthened E bound, q>=16 implies q^6>2q^4+4. No power-of-q
conclusion and no strict C>0 hypothesis has been used.

The index unit gives k=R+epsilon_k+hE. Since h>=1 and E>3,

    k>R+2, c>kY>2(R+2).                               (8)

Write P0=2XY^2+1. The first norm has the same classification as89:

    tau=chi_P0(n), k=2*psi_P0(n), n>=1,
    2n=R+epsilon_k modulo E,
    n>=(R+epsilon_k)/2>=(R-1)/2>=24.                       (9)

The congruence uses P0=1 modulo E and 0<R+epsilon_k<E. The main norm gives
c=psi_A(p), D=chi_A(p), p>=1. As P0>A and c>k, monotonicity forces

    p>=n+1>=25,
    c>(2A-1)^(p-1)>A^5>A*Delta^2, c>2p.              (10)

Apply the [generic strong-rank argument](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md)
to(5), equivalently T^2=Delta*(f^2-1). Its hypotheses are precisely the
main Pell equation and independently obtained c>A*Delta^2. It gives

    f=chi_A(m), c divides m, m>=c>2p,
    T=Delta*psi_A(m).                                 (11)

No equation involving the linear factor was used to obtain this rank.
Moreover f>chi_A(2p)=1+2*Delta*c^2>2c. Since o is positive,

    V=of-c>=f-c>0.                                   (12)

This recovers positivity of the changed auxiliary root before classifying
its Pell index.

## 4. Recovering the displaced main index

Define a temporary index target

    Jtarget=R+1-lambda, in {R,R+2}.                   (13)

The exact linear-unit identity L=lambda says

    V=U+lambda-1=jc-Jtarget.

At the same time V=of-c by definition. Equations(8),(10) give

    0<Jtarget<c/2, 0<p<c/2.                          (14)

By M3=1, (5), and(12), ordinary Pell classification at T gives ell>=1 with

    TV=chi_T(ell), y=psi_T(ell).

The index ell is odd, since chi_T(2v)=(-1)^v modulo T. Write ell=2v+1.
The integer polynomials from
[the half-parameter proof, Sections3–4](../../1980/HALF_PARAMETER_PELL_92_PROOF.md)
satisfy

    chi_T(2v+1)=T*Q_v(T^2),
    Q_v(1-A^2)=(-1)^v*psi_A(ell),
    Q_v(0)=(-1)^v*ell.                                (15)

Thus V=Q_v(T^2). As T^2=Delta*(f^2-1)=1-A^2 modulo f and V=of-c,

    (-1)^v*psi_A(ell)=-c modulo f.

Squaring and applying the doubling identity gives

    chi_A(2ell)=chi_A(2p) modulo chi_A(m).

The signed chi step-down lemma applies with 0<2p<m from(11), yielding
ell=+p or-p modulo m, hence modulo c. Independently T=ic^2 makes
Q_v(T^2)=Q_v(0)=(-1)^v*ell modulo c. Together with V=jc-Jtarget this
implies Jtarget=+p or-p modulo c. The strict size bounds(14) exclude the
negative alternative and all nonzero multiples of c. Therefore

    p=Jtarget=R+1-lambda.                             (16)

This argument is the ordinary signed-index proof with an explicitly
displaced target. It does not invoke the whole kernel theorem with a
changed index equation or assume either sign in advance.

## 5. Only the original pair of signs survives

We already know n<p from(10). Using(7) and(16),

    0<2n<2p<=2(R+2)<E.

Since 0<R+epsilon_k<E, the congruence in(9) is now exact:

    2n=R+epsilon_k,
    p-2n=1-lambda-epsilon_k.                              (17)

The possibilities are

| lambda=L | epsilon_k=Nk | p-2n |
|---:|---:|---:|
| 1 | 1 | -1 |
| 1 | -1 | 1 |
| -1 | 1 | 1 |
| -1 | -1 | 3 |

Every case except lambda=epsilon_k=1 has p>=2n+1. Let Q=chi_A(2)=2A^2-1.
The same positive parameter difference as90 gives Q>P0; also A>Y+1.
Pell duplication and monotonicity imply

    psi_A(2n)=2A*psi_Q(n)>=2A*psi_P0(n)=A*k.

If p>=2n+1, this forces

    c=psi_A(p)>A*k>k(Y+1),

contrary to kY<c<k(Y+1), which follows from c=kY+eta and
k=eta+zeta with both slacks positive. Hence

    L=Nk=1, Nt=1.                                   (18)

The last assertion follows from the product of signs in(6). Now V=U,
K=T^2, and all eight original89 factors are exactly1. This restores the
old89 equations on the same supplied tuple. Their theorem restores the
positive quotient z_old=zplus-1 and all eliminated positive witnesses,
proving soundness for the unchanged ordinary input.

Conversely a positive solution of89 has every original factor1, hence
V=U and K=T^2. Its modified M3 is the old auxiliary norm, and L=1. It
therefore satisfies(4) on precisely the same nineteen coordinates. The
two positive solution sets are identical; no coordinate shift, new input
coding, or new constraint on the fixed program is needed. The canonical
completeness and compiler margins are consequently inherited.

The order of the argument matters:

    N4=1 -> K=T^2 -> M3 is a unit Pell norm -> weak transport bounds
    -> both-sign first/main index bounds -> strong auxiliary rank
    -> V>0 and p=R+1-lambda -> exact first index -> L=Nk=Nt=1.

The root change without reversing the linear unit does not admit this
sign argument. At the formal kernel interface, start with U=V and Nk=1,
then replace a freely supplied R by R+2 while retaining the other kernel
values. Both Nk and `1+U-V` become-1, while the norm at V is unchanged.
This is an exact sign collision in that interface, not a counterexample
to a full packed compiler where R is computed from the outer variables.

## 6. Literal cost and original-source identity

The [checker](complete75_reversed_auxiliary89.py) and
[receipt](complete75_reversed_auxiliary89.json) give the full polynomial DAG.
Relative to89, exactly these three gate definitions change:

| Register | Before | After |
|---|---|---|
| `H2` | `H17*H17` | `aux_u_rhs*aux_u_rhs` |
| `L17` | `ic22*aux_square_gap` | `R16*aux_square_gap` |
| `linear_difference` | `H17-aux_u_rhs` | `aux_u_rhs-H17` |

Here H17=U, aux_u_rhs=V, ic22=T^2, R16=K. Every existing register remains
used. Reordering the DAG makes each new dependency available before use.
There are exactly88 certificate operations,48 multiplications and40
additions/subtractions, with the sole comparison `eight_units=1`.
The final unsquared subtraction of1 gives89=48M+41A. Binary arithmetic
with fixed numerals is charged; there is no extra equality, sign test,
or exponentiation primitive.

For the full original nineteen-residual identity, make the same formal
substitutions and `z_old=zplus-1` shift as89 Section6. Let its zero-based
residuals be r_i. In particular

    r12=T^2-K, r14=U-V,
    1+r13=T^2*(U^2-y^2)+y^2.

The modified auxiliary factor is identically

    M3=1+r13-T^2*r14*(U+V)-r12*(V^2-y^2).              (19)

The eight factors in(4) are therefore exactly

    1-r5, 1+r11, 1+r17,
    1+r13-T^2*r14*(U+V)-r12*(V^2-y^2),
    1+r8, 1+r2, 1+r12, 1-r14.                        (20)

The final polynomial is their product minus1. All deleted residuals still
vanish identically. Equations(19)--(20) hold off the zero set, including
signed assignments and z_old=0. They do not by themselves prove positive
zero-set equivalence; that is the ordered argument in Sections2–5.

## 7. Exact degree and checks

Give x and the nineteen supplied witnesses degree one. Fixed compiler
numerals have degree zero. Put Qtop=(B-1)J, k_top=eta+zeta, and

    C_top=Qtop-F-Z-alpha-2d*x.

The six unchanged factors retain their degrees and highest forms from89.
The modified factors have

    degree(M3)=28,
    M3_top=f^2*k_top^2*w^2*s^4*Qtop^18,
    degree(L)=6,
    L_top=-j*k_top*s*Qtop^3.                          (21)

Indeed K has degree18 with highest part f^2*w^2*s^2*Qtop^12; V has
degree5 with highest part -k_top*s*Qtop^3. The competing term K*y^2
has degree20, so it cannot cancel the degree28 term K*V^2. For L,
its degree6 term comes only from -jc.

The eight factor degrees are26,22,42,28,9,5,22,6, summing to160.
Their nonzero highest forms multiply to

    32*(B-1)^105*h*(rho+sigma)*delta^2*i^2*j*f^2
      *(eta+zeta)^10*w^13*s^22*J^105*C_top.             (22)

As C_top has F coefficient-1, this is nonzero for every admissible B.
Thus160 is the exact total degree, with no claim of a formal degree
reduction merely on the solution set.

Default execution regenerates and compares the receipt:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_reversed_auxiliary89.py

The checker verifies all gate dependencies and counts, the exact three
rewirings, and512 identities against both direct factor formulas and all
nineteen original residuals. The assignments include384 positive and128
signed supplied tuples at bases16,32,64,256. Signed tuples test polynomial
identities only. Four weighted, offset specializations check all factor
degrees and the exact coefficient(22); the auxiliary correction(19) is
also checked symbolically.

Additional checks cover all256 modified-norm residue assignments modulo4,
the four unit-sign branches,480 exact doubling
and ratio contradictions, and648 positive-root size fixtures. The checker
replays the inherited modulo4, signed negative-norm and odd-index polynomial
identities. These finite checks supplement the parametric proof and do not
construct complete accepting Pell witness towers. This is an explicit
compiler upper bound, with no global arithmetic optimum, real-zero-set
equivalence, or proof-assistant formalization claim.

Two independent reviewers passed the final proof, source and default receipt.
They checked the bootstrap for both index signs, the strengthened R+2 bounds,
rank before auxiliary classification, displaced-index recovery, three excluded
sign pairs, both directions of equivalence, exact counts and highest forms.
One reviewer separately replayed512 positive-supplied original19 identities
at bases16,32,128,512, including four deliberately negative computed mu values
and185 zero restored old quotients, then checked the degree160 leading form
with a weighted, offset specialization at B=128,d=7. The other independently
checked512 original19 identities, including four negative mu values and175
zero restored old quotients, plus three weighted, offset degree160 checks.
The index sign is written epsilon_k throughout to distinguish it from the
strictly positive supplied coordinate sigma.
