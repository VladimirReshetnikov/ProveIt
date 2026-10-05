# Reusing the scaled strong factor as an auxiliary coefficient gives no zeros

An apparently cheap reuse in the complete84 source fails maximally: replacing
the auxiliary coefficient by the negative scaled strong factor gives **no
positive zeros** on an authentic compiler slice. The two-row substitution
still costs84=47M+37A and retains all18 witnesses and every source row.
It does not improve the universal bound. The obstruction uses the normalized
strong rank and the literal auxiliary argument, without assuming the main
Pell index equals the compiler index.

## 1. Precisely the proposed source change

In the pinned complete84 source let

    X=wq, Y=sq^3, E=XY, k=eta+zeta, c=kY+eta,
    a=Y(X+1), A=a+2, Delta=A^2-1=a^2+4a+3,
    R=r_lhs, f=f, T=auxiliary_quotient, y=y_aux,
    V=c*(T*f-1)-R*f^2, S=i*Delta*c^2,
    Ns0=f^2-Delta*i^2*c^4, Ns=Delta*f^2-S^2=Delta*Ns0.

The existing auxiliary norm is

    Na_old=S^2*(V^2-y^2)+y^2.

The proposed replacement reuses the already paid Ns register:

    Na_new=y^2-Ns*(V^2-y^2).                         (1)

Specifically replace exactly these two rows:

    L17 = R16 * aux_square_gap
    norm_aux = L17 + aux_y2

by

    L17 = norm_strong * aux_square_gap
    norm_aux = aux_y2 - L17.

All other82 rows, supplied ports and the product-minus-Delta finalizer
are literal. Both new dependencies are available in the existing order.
S and S^2 remain live through Ns; this change saves no gate by itself.
The full child source is included as inert data in the companion JSON.

Let P5 be the unchanged product of the first, main, input, index and
transport factors. The whole child polynomial has the all-ring identity

    F_bad=P5*Na_new*Ns-Delta
         =Delta*(P5*Na_new*Ns0-1).                 (2)

No assertion that F_bad equals the old polynomial is made. In particular,
one cannot use the accepted complete84 zero theorem for this child.

## 2. What follows before any auxiliary-index argument

Every supplied coordinate is a positive integer. On an authentic fixed
program slice q>=16, X,Y,a are positive, and Delta>0 before any equation.
If F_bad=0, cancellation in (2) makes each of the seven integer factors
inside the parentheses a unit. Delta is0 or3 modulo4, so a norm
r^2-Delta*t^2 cannot be-1. Thus the unchanged main and normalized strong
factors are+1, in particular

    D^2-Delta*c^2=1,
    f^2-Delta*i^2*c^4=1,
    Ns=Delta.                                      (3)

After substituting Ns=Delta in (1), its unit equation is

    Na_new=(Delta+1)*y^2-Delta*V^2
          =(A*y)^2-Delta*V^2=1.                   (4)

The same modulo4 argument excludes-1 here. This step does not use the
old auxiliary sign or index theorem, which no longer applies.

The unchanged transport factor is

    Nt=(K+w)*C+U-t*(q-1),
    U=q-F, C=U-Z-alpha-2dx.

It is a unit, and U-t*(q-1)=1-F-(t-1)*(q-1)<=0. Since K+w>=2,
C<=-1 would give Nt<=-2. Hence C>=0. The literal authentic packing/mask
argument, requiring only this inequality and positive supplied outer
coordinates, gives

    (2q-1)*(q^2-1)<R<q^4-q^3.                      (5)

The index unit k-hE-R=+/-1, with h>=1 and E>1, gives k>R and therefore

    0<R<c, c>2.                                    (6)

These bounds are the pre-decoding bounds from Section2 of the direct-X
boundary note, with X=wq and the original transport factor. They do not
require any old auxiliary equation, a decoded input or a dyadic q.

## 3. The incompatible Pell divisibilities

For Delta=A^2-1, A>=2, use chi_A(j),psi_A(j) for the integer coefficients
of (A+sqrt(Delta))^j. The positive-coefficient Pell classification applied
to (3), using the unchanged positive main root D, gives

    D=chi_A(p), c=psi_A(p), p>=2,
    f=chi_A(m), psi_A(m)=i*c^2, m>=1.              (7)

The normalized divisibility lemma gives

    p*c divides m, in particular p divides m and m>2p. (8)

For completeness, strong divisibility of psi first gives p|m. Write
m=pj and D=chi_A(p). Composition gives psi_A(m)=c*psi_D(j).
Modulo c, D^2=1 and psi_D(j)=j*D^(j-1). Since D is a unit modulo c,
c|psi_D(j) forces c|j. This proves (8); it uses no main-index recovery.

Equation (4) has A*y>1, so V is nonzero. Pell classification now gives

    A*y=chi_A(ell), |V|=psi_A(ell), ell>=1.         (9)

No sign or parity of ell is needed. The literal V gives V=-c modulo f.
Squaring, using (7) and (9), and using chi_A(2j)=1+2Delta*psi_A(j)^2
yields

    chi_A(2ell)=chi_A(2p) modulo chi_A(m).          (10)

The signed chi step-down lemma applies because 0<2p<m, giving
2ell=+/-2p modulo2m, hence ell=+/-p modulo m. By (8), p divides ell.
Pell composition therefore implies

    c=psi_A(p) divides psi_A(ell)=|V|.             (11)

On the other hand, (3) gives f^2=1 modulo c, while the unchanged literal
argument gives V=-R*f^2 modulo c. Thus (11) forces c|R, contradicting
0<R<c in (6). There is no positive zero.

## 4. Retained failed proposal and scope

**Review remark 1 (same-discriminant coefficient reuse is refuted).**
The proposal that the paid negative scaled strong factor could replace
the positive square auxiliary coefficient while preserving universality
is false: (1)--(11) prove its positive zero set empty on every authentic
compiler slice, including programs accepting some input. The apparent
reuse turns the auxiliary equation into a Pell equation in the same
discriminant as the main/strong pair. Its two retained congruences then
force the impossible divisibility c|R. This proves failure for the exact
two-row replacement, not a lower bound for arbitrary auxiliary designs.

In particular, the proof never invokes p=R from the old auxiliary argument,
never infers V>0, and never treats the modified source as a parent zero.
It proves neither a new small universal polynomial nor a counterexample
to the separate open direct-X83 construction. The existing universal84
source and all frozen predecessor bytes remain unchanged.

The companion JSON authenticates the four primary dependency notes/source,
binds this note, and records both edited rows, the full84-row inert child,
its topology, counts and all-port liveness. The proof depends on the
explicit pre-decoding outer bounds, normalized divisibility and signed
step-down lemmas in those dependencies; it does not claim a new audit of
their entire literature ancestry. No saved source array was evaluated,
no predecessor scientific program was executed or imported, and no
numerical zero fixture or symbolic source interpreter was used. Only
fresh static row/count/binding work accompanied this handwritten proof.
