# A coupled auxiliary linear unit saves two more polynomial additions

The [native index-unit rewrite](group_projective_index_unit.md), applied
to the [joint-bound and first-root compiler](group_projective_joint_first_norm.md),
has a further complete ordinary-input successor. It uses the auxiliary
root `V=of-c` directly and couples its linear index to the already paid
difference `K=k-hE`. Three old additions are replaced by three additions;
one multiplication merges the new linear unit and removes one comparison.
The single SOS polynomial saves **two additions** beyond the index-unit
successor, or three beyond the joint-bound/first-root composition.

The new system permits a negative index/checksum branch. That branch
normalizes to a positive parent certificate by changing only three
native coordinates. All outer history, controller, selected-source and
ordinary-input values remain fixed. The theorem is accepted-input
equivalence; it is not a positive-tuple bijection or a claim that every
new unit equals one.

Keep the fixed positive compiler numerals and `alpha+beta+1>=m`. Write

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1,
    nu=1+chi.

Here epsilon is the controller-mask option, requiring m>=8, and chi
is the computed-P option. The complete bounds are

| Computed native fields | Certificate | Equations | Positive witnesses | SOS polynomial | Exact degree |
|---|---:|---:|---:|---:|---:|
|a,d,k,s|C+4|14-chi|m+33-chi|C+45-3chi|24nu L+54|
|a,c,d,k,r,s|C+4|12-chi|m+31-chi|C+39-3chi|nu(40L+2m+30)+60|

For the illustrative ten-letter table, m=16,h=4,p=4,f_flow=19 and
epsilon=chi=1 give C=258. The six-field successor has **262 certificate
operations, 11 equations, 46 positive witnesses and a 294-operation
polynomial of exact degree 3544**. This is an illustrative fixed table,
not an instantiated numerical universal alphabet. The separate 75/88
numerical frontiers remain unchanged.

## 1. The six units and the exact source change

Use the native quantities

    X=wq, Y=sq, E=XY, k=eta+zeta, c=kY+eta,
    a=Y(X+1), A=a+2, Delta=A^2-1,
    T=ic^2, K=k-hE, V=of-c.

Both ratio slacks stay positive, so

    kY<c<k(Y+1).                                  (1)

The old auxiliary root is `U=jc-(2r+1)`. Replace it in the auxiliary
norm by V and introduce the linear unit

    N0=g^2+4XY^2k(g-k),
    N1=d^2-Delta*c^2,
    N3=T^2(V^2-y^2)+y^2,
    Q=q-(F0+F1+F2+F3),
    Nk=K-r, Nl=V-jc+2K.                           (2)

The new comparison is

    N0*N1*N3*Q*Nk*Nl=1.                           (3)

The strong comparison `T^2=Delta(f^2-1)` is retained. The separate
linear comparison `U=V` is deleted. All other outer and native
comparisons remain exactly as before.

The [literal source](group_projective_coupled_linear_unit.py) first
applies the index rewrite to the actual joint-bound/first-root packet.
The index rewrite already supplies `K=selection__R11`. The coupled
rewrite deletes exactly

    r1=r+1, tr1=r1+r, U=jc-tr1,

changes the input of the existing square from U to V, and adds

    twice_K=K+K, linear_difference=V-jc,
    Nl=linear_difference+twice_K,
    six_units=five_units*Nl.

The source checks every consumer of the three deleted registers: r1
is used only by tr1, tr1 only by U, and U only by its square and the
deleted comparison. All gates computing `of`, V, jc and K were already
paid. There is no extra multiplication for the numeral two. Thus this
rewrite adds exactly one multiplication and removes one comparison at
unchanged addition and witness counts.

## 2. Bounds before any native typing

On a positive zero the joint-bound argument first restores both
positive scalar bounds. It also proves P>=12, J>0 and the positive
geometry needed by the existing source. Independently of checksum
typing, `q=16P^L>=16`, X,Y,k are positive, and F0,F1,F2 are positive
supplied fields. The fourth field is positive from its actual padded
definition `F3=16Z_joined+8`, whose joined output is nonnegative.

The three norms in (2) cannot equal -1 modulo four on any integer
assignment. For N0 this follows from `N0= g^2 mod4`. For N1,
`Delta=0 or3 mod4`; for N3, `T^2=0 or1 mod4`, so the norm is congruent
to `y^2` or `V^2`. These exclusions do not use positivity or another
equation. Equation (3) therefore gives signs epsilon_k,lambda in {-1,1}
with

    N0=N1=N3=1, Nk=epsilon_k, Nl=lambda,
    Q=epsilon_k*lambda, K=r+epsilon_k.             (4)

Keep epsilon_k distinct from the controller-mask option epsilon.
At this point Q need not be positive. The packing and retained bound
still give

    r=F0+qF1+q^2F2+q^3F3, X=r+bound_beta>r.

Since the positive field sum is q-1 or q+1, the same elementary
estimate as in the index proof gives

    q^3+q^2+q+1<=r<q^4, r>=4369,
    Y>=q>=16, E>2r+3.                             (5)

No bit partition, power-of-two conclusion or decoded word is used.
For the eventual main target set

    Jnew=2K-lambda=2(r+epsilon_k)-lambda,
    2r-3<=Jnew<=2r+3.                             (6)

The positive inverse first-root map restores the triangular Pell
equation from N0=1. Its elementary classification, with
`Pfirst=2XY^2+1`, gives

    k=psi_Pfirst(n), n>=1,
    n=K mod E, n>=r-1.                            (7)

The congruence follows from Pfirst=1 mod E, and the last bound follows
because `0<r+epsilon_k<E`. From N1=1 and the positive main root,
`c=psi_A(p), d=chi_A(p)`. As Pfirst>A and c>k, monotonicity forces
p>n. Thus p>=r and the standard Pell growth bounds give

    c>A*Delta^2, c>2p,
    c>Yk>=Y(r-1)>2(2r+3).                         (8)

The last strict inequality uses just Y>=16 and r>=4369. In particular
both p and Jnew lie strictly between zero and c/2. These estimates
precede checksum/index sign recovery or use of the full native typing
theorem.

## 3. Recovering the linear sign

Apply exactly the integral-rank and divisibility lemmas used in
[the index-unit proof, Section 3](group_projective_index_unit.md#3-recovering-the-main-index-from-the-unchanged-strong-equations).
Their hypotheses are the retained strong equation, `c=psi_A(p)`,
`c>A*Delta^2`, and positive i. They give an auxiliary index ell_aux with

    f=chi_A(ell_aux), c divides ell_aux,
    T=Delta*psi_A(ell_aux), ell_aux>=c>2p.          (9)

Consequently `f>chi_A(2p)=1+2Delta*c^2>2c`. Since o>=1, the new
auxiliary root is now known positive:

    V=of-c>0.                                    (10)

This step is essential: its positivity is proved before using the
normalized positive Pell classification, rather than assumed from
the signed expression of-c.

The norm N3=1 is

    (TV)^2-(T^2-1)y^2=1.

Because T>1 and V,y>0, the same odd-index argument as in the index
proof gives an odd ell=2v+1 and

    V=(-1)^v psi_A(ell) mod f,
    V=(-1)^v ell mod c.                           (11)

Here `V=of-c` gives V=-c mod f, while Nl=lambda gives
`V=jc-Jnew` and V=-Jnew mod c. Squaring the first congruence and
using chi doubling yields
`chi_A(2ell)=chi_A(2p) mod chi_A(ell_aux)`. The retained signed
chi step-down lemma applies with `0<2p<ell_aux`, giving
`ell=+p or-p mod ell_aux`, hence modulo c. Combining with the second
congruence gives `Jnew=+p or-p mod c`. The strict bounds (8) exclude
the negative alternative and nonzero multiples of c. Therefore

    p=Jnew=2K-lambda.                             (12)

Since `n<p<=2r+3<E`, (7) now forces n=K. If lambda=-1 then
p=2n+1. Put `Q2=chi_A(2)=2A^2-1`. The exact inequalities
Q2>Pfirst and 2A>Y+1 give

    psi_A(2n)=2A*psi_Q2(n)
              >=2A*psi_Pfirst(n)=2Ak>k(Y+1).

Then c=psi_A(2n+1)>psi_A(2n), contradicting (1). Hence

    Nl=1, Q=Nk=epsilon_k,
    p=2K-1, n=K.                                 (13)

This proof ports the individual rank and signed-index lemmas with
the enlarged target bounds (6), not the complete old native theorem
with Q=1 assumed. The index sign epsilon_k has intentionally not
been excluded.

## 4. Positive normalization of both index signs

If epsilon_k=1, then K=r+1, Q=1 and Nl=1 gives
`V=jc-(2r+1)=U`. Every parent comparison is restored unchanged.

If epsilon_k=-1, the retained input-port comparisons and q=0 mod16
give

    F3=8, F1=4, F2=2 mod16,
    F0=3 mod16.                                  (14)

Indeed `F1+F3=16H_joined+12`, `F2+F3=16M_joined+10`, and the
negative checksum says `F0+F1+F2+F3=q+1`. Positivity thus gives
F0>=3, without Boolean typing. Define

    F0'=F0-2>0, r'=r-2>0,
    bound_beta'=bound_beta+2>0.                   (15)

All other supplied coordinates are unchanged. In the four-field
variant r is supplied and is changed explicitly. In the six-field
variant the actual packed-r definition recomputes r-2 automatically.
The input-port comparisons do not use F0, so they remain identical.
The packing, checksum and bound become

    r'=F0'+qF1+q^2F2+q^3F3,
    Q'=1, r'+bound_beta'=X.

Also `K=r-1=r'+1` and

    jc-(2r'+1)=jc-(2r-3)=V,

the last equality following from Nl=1 and K=r-1. Thus the old
auxiliary root is exactly V and every norm and strong equation is
unchanged. This restores a positive zero of the complete index-unit
parent, which in turn restores the earlier complete compiler. All
outer fields, scales, histories, selectors, input x and fixed compiler
numerals stay unchanged.

Conversely, every positive zero of the complete joint-bound/first-root
parent has Q=Nk=1 and U=V. It gives Nl=1 and satisfies the new product
with the same supplied coordinates. These two directions prove exact
accepted-input equivalence. The normalization (15) can identify
different native tuples, so no graph-bijection claim is made.

The special universal fixed table and the padded enumeration are
inherited unchanged. The normalization is internal to its native
AND verifier and does not recode the ordinary input or require an
extra controller, bound or length hypothesis.

## 5. Off-zero identities and the arithmetic ledger

Let the immediate index parent have auxiliary root U, linear residual
`r_lin=U-V` and five-unit product. On arbitrary supplied integer
assignments, including signed ones, the new quantities satisfy

    N3_new=N3_old+T^2(V^2-U^2),
    Nl=2Nk-1-r_lin.                              (16)

The new product residual is exactly

    N0*N1*[N3_old+T^2(V^2-U^2)]*Q*Nk*
        [2Nk-1-r_lin]-1.                         (17)

Every other retained residual is identical. These identities do not
use the sign proof or divide by a norm factor. On structured assignments
with `Q=Nk=epsilon_k` and Nl=1, normalization (15), with delta=1-epsilon_k,
makes every restored parent residual match the new residual list; the
deleted linear residual is zero. Therefore the two full SOS values
are identical on that conditional locus even when the Pell residuals
are nonzero. The checker audits both kinds of identity separately.

Relative to the joint-bound/first-root packet, the index rewrite costs
1M+1A and removes one equation; the coupled rewrite costs1M and
removes another. Together they save three SOS additions. Relative to
the padded-program certificate C, the final certificate split is

    M=m+2h+85+f_M-d_M-epsilon,
    A=2m+h+p+104+f_A-d_A.

The SOS splits are

    four: M=m+2h+99+f_M-d_M-epsilon-chi,
          A=2m+h+p+131+f_A-d_A-2chi;
    six:  M=m+2h+97+f_M-d_M-epsilon-chi,
          A=2m+h+p+127+f_A-d_A-2chi.

The inherited shared-register savings are `(d_M,d_A)=(1,2)` for h=1,
`(3,3)` for h=2 and `(5,4)` for h>=3. Supplied coordinates are
unchanged. The complete source counts every fixed-numeral multiplication
and every residual subtraction, square and summation addition.

## 6. Exact degree in the actual supplied coordinates

All supplied coordinates, including x, have degree one; fixed compiler
numerals have degree zero. Use the widened-radix highest parts

    P*=P if supplied,
    P*=16(alpha*x+height_slack)*sum_e Ehat_e if computed,
    q*=16(P*)^L, s*=2*odd_half, k*=eta+zeta,
    a*=w*s*(q*)^2.

The first and linear units have highest parts

    N0*=4w(s*)^2(q*)^3 k*(g-k*), degree 3nu L+5,
    Nl*=-2h*w*s*(q*)^2, degree 2nu L+3.           (18)

For four computed fields, c and r remain supplied. Then V*=of,

    N1*=8ga(a*)^2(c+2ga), degree 4nu L+6,
    N3*=i^2 c^4 o^2 f^2, degree 10,
    Nk*=-h*w*s*(q*)^2, degree 2nu L+3.            (19)

For six computed fields set

    c*=k*s*q*, r*=16^4 H2(P*)^(3L+m+15).

Here V*=-c*, and

    N1*=8ga(a*)^2c*, degree 5nu L+7,
    N3*=i^2(c*)^6, degree 6nu L+14,
    Nk*=-r*, degree nu(3L+m+15)+1.                (20)

In both variants Q*=q*, of degree nu L. Multiplying the six nonzero
highest forms gives the unique largest residual degree. The SOS has
the square of that product as its nonzero highest homogeneous part.
Adding the degrees gives exactly the opening table. The cancellations
inside N1, including c+2ga in the four-field variant, are already
included in (19)-(20). No on-zero relation is substituted to reduce
degree. In particular, replacing U by V is the actual source change,
not a use of the deleted linear comparison during degree calculation.

## 7. Executable evidence and scope

The [receipt](group_projective_coupled_linear_unit.json) records twenty
compact ledgers and one full ten-letter source. The checker verifies
the removed-register consumer sets, every literal residual and full
numeric SOS against (16)-(17), on 1,280 assignments including 320
signed assignments. All twenty variants receive exact weighted offset
polynomial evaluations of their certificate residuals and all six
individual unit factors. Degree and leading coefficient are checked
before the final square; the checker does not expand the redundant
full SOS symbolically.

Separately, 512 conditional normalization fixtures cover both index
signs, both field variants, both mask variants and both P options.
There are 384 positive restorations and 128 signed off-zero identities.
They keep every outer register fixed and compare the entire restored
parent residual list and SOS. These are structured algebraic checks,
not claims to have materialized the enormous positive Pell witnesses.
The parametric proof supplies those witnesses and the sign recovery.

Finite padding-residue and weak-target-bound checks supplement the
proof, with no bounded-search claim about decidability. Run the source
normally to compare its deterministic receipt, or use `--write` to
regenerate it. All parent packets remain unchanged.

The author regenerated the receipt and ran a fresh default replay; both
passed. Three independent reviewers read the full proof and actual
source with no findings after a wording clarification about sign-recovery
order. Their checks covered the pretyping hypotheses, both normalization
branches, all affected consumers, literal ledgers and six highest forms.
One reviewer additionally evaluated all six factors directly from the
scalar equations and the full SOS on 512 signed assignments, and checked
256 positive conditional restorations. Another independently checked
256 positive actual-DAG restorations while also enforcing both physical
input ports and the native X bound. These additional fixtures are
structured off-zero norm tuples, not materialized full Pell zeros.
