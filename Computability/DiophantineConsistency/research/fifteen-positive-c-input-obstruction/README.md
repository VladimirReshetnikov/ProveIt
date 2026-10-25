# The fifteen-positive C-input shortcut loses a pointwise alpha bound

The literal 66-operation, degree157 source has a tempting one-gate shortcut:
replace its positive alpha input by a positive C input, delete the definition
C=q-F-alpha, and compute the packing gap as q(q-F)-C. This note proves a
precise limitation of that shortcut. **Conditionally on any canonical
positive source witness, the broadened polynomial has positive witnesses
whose recovered alpha=q-F-C and packing rank R are both negative.** The
construction retains exactly the same whole four-port coefficient tuple.

This is an ordinary, code-free conditional theorem. It does not produce an
unconditional zero, disprove existence-equivalence of the broadened
polynomial, rule out another normalization theorem, or certify a new
65-operation consistency equation. There is no new program, equation JSON,
Lean result, TeX or PDF here. SOURCE_PINS.json fixes the complete literal
source and the retained ordinary/native contracts; MANIFEST.json closes
these two local payloads.

## 1. Exact source and proposed virtual change

The literal source is
`con-zfc-diophantine-forms/54-calibrated-carry/positive/p66_degree157.json`.
Its fifteen strictly positive inputs are

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.

Its four fixed positive ports are beta,K0,MC,MF; MF means MF_source, shifted
once. All other letters below are polynomial abbreviations, not witnesses:

    qm=beta J, q=qm+1, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a^2+H, D=X+ac+gamma H, S=i Delta c^2,
    C=q-F-alpha,
    R=[qm(q-F)+alpha](q^2-1)+(MC+q MF)J,
    V=f^2(cT-R)-c,
    ell=E kY,
    N0=tau^2-ell(ell+k), N1=D^2-Delta c^2,
    Na=S^2(V^2-y^2)+y^2,
    Nk=k-hE-R, Nt=(K0+w)C+(q-F)-z qm,
    Ns=Delta f^2-S^2.

The polynomial is

    P=N0 N1 Na Nk Nt Ns-Delta.

The proof in SHORT_COMPOSITIONS_PROOF.md section8 retains the ordinary
source/rank theorem and squared-modulus reconstruction. The original
source54 tuple is the coherent89x4831 tuple. Its polynomial may also be
specialized, as a whole, to the indexed943 tuple by composing the complete
normalized-positive interface in indexed-tile-enumeration/PROOF.md section4
with that same section8 and the R=3 modulo4 canonical reconstruction.
The pinned page-feasibility note states this composition and distinguishes
the two tuples. This note neither equates them nor mixes their ports.

The proposed virtual shortcut replaces alpha in the input list by C>0,
deletes the producer [C,-,qF,alpha], and replaces only

    [gap_product,*,qm,qF]  by [gap_product,*,q,qF],
    [gap,+,gap_product,alpha] by [gap,-,gap_product,C].

Here qF=q-F. These are all the source's alpha occurrences. All other
producers stay unchanged. Indeed

    qm(q-F)+alpha=q(q-F)-C

whenever alpha=q-F-C. The virtual arithmetic ledger would be
38 products,14 sums,13 differences,65 operations. That count describes
the local edit only and supplies no missing domain theorem. No edited DAG
or accepted endpoint is emitted here.

## 2. Conditional canonical premises

Start from any canonical positive source witness with C>0, R>0,

    N0=N1=Na=Nk=Nt=1, Ns=Delta,
    Delta=(a+2)^2-1, f^2=1+Delta i^2 c^4,
    R=3 modulo4, c=psi_(a+2)(R).

For an authentic whole native tuple, its ordinary completeness theorem
provides these premises from a finite syntactic ZFC refutation. They are
conditional data in the argument, not a claim that a refutation exists.
The canonical auxiliary reconstruction may be chosen as

    S=Delta i c^2>1,
    j0=(R-1)/2,
    V0=chi_S(R)/S=Q_j0(S^2)>0,
    y0=psi_S(R)>0,
    T0=(V0+c+R f^2)/(c f^2)>0.

Here chi,psi are the usual Pell sequences for parameter S and

    Q_0(x)=1, Q_1(x)=4x-3,
    Q_(j+1)(x)=(4x-2)Q_j(x)-Q_(j-1)(x).

The squared-modulus proof establishes this choice, including integrality
and the exact identity V0=f^2(cT0-R)-c. All its outer and fixed coordinates
remain unchanged below.

## 3. Positive F,C,h,z shifts preserve the two carrier factors

Put

    L=E qm c>0, d=(q^2-1)(q+1)>0.

For each integer m>=0 set

    F_m=F+mL, C_m=C+mL,
    R_m=R-d mL,
    h_m=h+d m qm c,
    z_m=z+(K0+w-1)mEc.

All four supplied coordinates F_m,C_m,h_m,z_m are strictly positive:
q>1 and K0,w>0 imply K0+w-1>=1. The rank expression in the broadened
C-input polynomial gives exactly the displayed R_m, since

    q(q-F_m)-C_m=q(q-F)-C-(q+1)mL.

The fixed mask term (MC+q MF)J is identical. Direct subtraction gives

    h_m E+R_m=hE+R,
    (K0+w)C_m+(q-F_m)-z_m qm=Nt=1.

For the second identity the increment before the z term is
(K0+w-1)mL and L=E qm c. Consequently Nk remains1 as well. The recovered
old input is

    alpha_m=q-F_m-C_m=alpha-2mL.

Thus both alpha_m and R_m are strictly negative for all sufficiently
large m. No lower bound for R_m, and no equality R_m=R, is assumed.
Also R_m-R is a multiple of c. The first and main norms, every retained
outer coordinate, all four fixed ports, and Ns=Delta are unchanged.

## 4. A fresh auxiliary index restores positive T and y

One cannot keep V0 and merely shift T: that would eventually make T
negative. Instead use a fresh auxiliary Pell index while retaining the
same S,c,f. Let M=c f^2>0 and consider the integer recurrence matrix

    A=[[4S^2-2,-1],[1,0]], det(A)=1.

Its reduction modulo M lies in the finite group GL_2(Z/MZ), so some
integer p>0 satisfies A^p=identity modulo M. For j>=1,

    [Q_j(S^2),Q_(j-1)(S^2)]^t
      =A^(j-1)[Q_1(S^2),Q_0(S^2)]^t.

Since j0>=1, for every t>=0 the index j_t=j0+pt satisfies

    Q_j_t(S^2)=V0 modulo M.

Define

    n_t=2j_t+1,
    V_t=Q_j_t(S^2)=chi_S(n_t)/S,
    y_t=psi_S(n_t).

These are positive integers, and the Pell identity gives

    S^2(V_t^2-y_t^2)+y_t^2=1.

Moreover V_t tends to infinity: the positive sequence chi_S(n) is strictly
increasing and unbounded for integer S>1, and n_t tends to infinity.
For each fixed m, put

    T_(m,t)=(V_t+c+R_m f^2)/(c f^2).

This is an integer. Its numerator differs from the known multiple
V0+c+R f^2 of c f^2 by

    (V_t-V0)+(R_m-R)f^2,

and both summands are multiples of c f^2. Choose t sufficiently large
that the numerator is positive. Then T_(m,t)>0 and

    f^2(c T_(m,t)-R_m)-c=V_t.

Thus the actual broadened source's auxiliary factor remains1 with the new
positive T_(m,t),y_t. This period argument uses the full fixed modulus
c f^2, not a prime or squarefree surrogate. It does not change the main
index R or confuse it with the new negative packing value R_m. The fresh
auxiliary index n_t need not equal either.

## 5. Consequence and limit

Keep J,f,i,s,w,tau,eta,zeta,gamma unchanged; supply instead

    F_m,C_m,z_m,h_m,T_(m,t),y_t.

These, together with the retained coordinates, are all fifteen positive
inputs of the broadened polynomial. Every factor equals its canonical
value, so its product is Delta and its polynomial is zero. For large m
the recovered alpha_m and computed R_m are negative. In particular

    finite refutation
      => broadened positive zeros with alpha_m<0 and R_m<0.

A pointwise assertion that every such zero recovers alpha>0 is therefore
not a neutral domain-restoration lemma: combined with ordinary canonical
completeness it would imply Con(ZFC). The shortcut cannot be accepted on
that proposed premise. The statement is deliberately conditional. It does
not show that the broadened equation has a zero when ZFC is consistent,
and it does not preclude a different existential normalization or another
encoding that gives a sound 65-operation consistency equation.
