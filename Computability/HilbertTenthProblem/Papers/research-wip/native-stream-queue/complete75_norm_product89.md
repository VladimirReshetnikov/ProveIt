# Eight integer units give an unsquared 89-operation universal polynomial

The fixed complete75 compiler admits a single polynomial with **19 strictly
positive existential witnesses**, exact total degree **166**, and evaluation
cost **89=48M+41A**. The same ordinary positive input x and fixed program
numerals are retained. Its comparison certificate costs **88=48M+40A** and
has one equation. The best complete comparison bound remains75.

Starting with [norm product90](complete75_norm_product90.md), convert its
remaining two auxiliary comparisons into unit factors. A congruence modulo4
excludes the negative strong-auxiliary unit. A folded Pell-residue argument
then excludes the negative linear-auxiliary unit, before the90 theorem is
invoked. There is finally one product equation, so its residual itself is
the output polynomial; no square is needed. This improves both the operation
count and degree of90/degree276. The smaller-degree96/84 and94/96 constructions
remain different tradeoffs.

## 1. Coordinates, fixed numerals, and literal factors

Keep all fixed compiler numerals and conventions of90: B>=16, positive
input constants d,b, and mask numerals 0<MC,MF<B-1. Write K0=DC+B*DR.
The supplied positive coordinates are exactly

    J,F,alpha,zplus,f,h,i,j,o,s,w,tau,eta,zeta,y,Z,delta,rho,sigma.

The source names are Jrep and y_aux for J and y. All intermediate expressions
below are substituted into the circuit, rather than supplied as additional
coordinates:

    q=(B-1)J+1, X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, a=E+Y, c=kY+eta,
    A=a+2, H=4a+3, Delta=a^2+H=A^2-1,
    D=X+ac+(rho+sigma)H,
    C=q-F-Z-alpha-2d*x, W=C-Z,
    kappa=2d*x+b+delta*Delta, mu=W+a*kappa+rho*H,
    G=(q-1)(q-F)+(q-F-Z)=q^2-Z-qF,
    R=G*(q^2-1)+(MC+q*(MF+B-1))*J,
    T=i*c^2, U=jc-R.                                      (1)

Here A is a proof abbreviation; the literal register `A` stores Delta.
Computed C,W,R,mu,U can be signed away from the zero set. There is no
uncharged sign comparison in the polynomial. Define eight integer factors:

    N0=tau^2-(E^2+X)(kY)^2,
    N1=D^2-Delta*c^2,
    N2=mu^2-Delta*kappa^2,
    N3=T^2*(U^2-y^2)+y^2,
    Nk=k-R-hE,
    Nt=(K0+X)C+(q-F)-zplus*(q-1),
    N4=1+T^2-Delta*(f^2-1),
    Nl=1+U-of+c.                                          (2)

The final output is the single, generally signed polynomial

    P89=N0*N1*N2*N3*Nk*Nt*N4*Nl-1.                        (3)

All arguments below concern integer zero sets. No real-witness equivalence
or equality with the former sum of squares is asserted.

## 2. Unconditional sign exclusions

The integer negative-Pell descent lemmas in
[91, Section1](complete75_norm_product91.md) exclude solutions of

    u^2-(A0^2-1)v^2=-1 for A0>=2,
    u^2-V(V+1)v^2=-1 for V>=2,                            (4)

including signed u,v. They apply independently of every other equation:
N0 uses V=XY^2>1, N1 and N2 use A0=A, and
`N3=(TU)^2-(T^2-1)y^2` uses A0=T=ic^2>=9.
Thus N0,N1,N2,N3 cannot be-1 on the positive supplied domain, even when
mu or U is negative.

There is also an unconditional exclusion **N4 cannot be-1**, requiring
only that A,T,f are integers. Indeed N4=-1 would imply

    T^2+2=(A^2-1)(f^2-1).                               (5)

If A is odd, the right side is0 modulo4, requiring T^2=2 modulo4.
If A is even, Delta=3 modulo4. For odd f the same contradiction holds;
for even f, (5) requires T^2=3 modulo4. Neither residue is a square.
This proof allows arbitrary signed supplied values and does not assume
the strong auxiliary equation. The positivity needed by the other four
norm exclusions is separate.

If P89=0, each of its eight integer factors is1 or-1. Therefore

    N0=N1=N2=N3=N4=1,
    Nk,Nt,Nl in {1,-1}, Nk*Nt*Nl=1.                     (6)

In particular the full strong auxiliary equation has already been restored:

    T^2=Delta*(f^2-1).                                  (7)

## 3. Bootstrap for both possible index signs

No linear auxiliary equality is assumed in this section. Let Nt=epsilon_t
with epsilon_t in{1,-1}. Its definition gives

    (K0+X)C=F+(zplus-1)(q-1)+(epsilon_t-1)>=-1.          (8)

Since K0+X>1 and C is integral, C>=0. From its definition, positive alpha
and x give F+Z<q. The same elementary packing estimates as
[90, Section3](complete75_norm_product90.md) consequently give

    2q-1<=G<=q^2-q-1,
    0<(MC+q*(MF+B-1))*J<(q-1)(1+2q),
    (2q-1)(q^2-1)<R<q^4-q^3<q^4.                      (9)

In particular R>3q+1. These inequalities do not require q to be a power
or C to be strictly positive. The C=0,Nt=-1 partial fixture in90 remains
relevant at this stage.

Now write Nk=epsilon_k in{1,-1}, so

    k=R+epsilon_k+hE.                                  (10)

We have X,Y>=q^3, E>=q^6>2R, and a=Y(X+1)>R. Thus
`0<R+epsilon_k<E`, and k>R because h>=1 and E>1. Set P0=2XY^2+1.
The first-norm classification from
[half-binomial42, Section3](pell_kernel_half_binomial42.md) gives

    tau=chi_P0(n), k=2*psi_P0(n), n>=1.                 (11)

Its fundamental unit has coefficient2, not1. Since P0=1 modulo E,
`psi_P0(n)=n modulo E`; hence

    2n=R+epsilon_k modulo E,
    n>=(R+epsilon_k)/2>=(R-1)/2>=24.                    (12)

The positive main norm gives c=psi_A(p), D=chi_A(p), p>=1. The available
X,Y>=q^3 imply P0>A. Monotonicity in the Pell parameter and index, together
with c>k=2*psi_P0(n), forces p>=n+1>=25. Standard recurrence growth gives

    c>(2A-1)^(p-1)>A^5>A*Delta^2, c>2p.               (13)

Also c>kY>2R, so U=jc-R>0. These are precisely the generic hypotheses of
the [relaxed auxiliary-rank proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md).
Applied to (7), its integrality and divisibility argument gives

    f=chi_A(m), c divides m, m>=c>2p,
    T=Delta*psi_A(m)>1.                                (14)

This use of the rank theorem requires neither Nl=1 nor an exact value
of p. Its argument depends only on the main norm, the size bound
c>A*Delta^2, and the strong auxiliary square. Thus (14) has been established
for either sign in(10), before restoring the linear auxiliary equation.

## 4. Folding Pell residues excludes the linear negative unit

We use the standard recurrences `chi_A(0)=1, chi_A(1)=A`,
`psi_A(0)=0, psi_A(1)=1`, and `z(n+2)=2A*z(n+1)-z(n)`.
For any integers A>=3,m>=1, put f=chi_A(m). The doubling identities give

    chi_A(2m)=2f^2-1=-1 modulo f,
    psi_A(2m)=2f*psi_A(m)=0 modulo f.

Addition and subtraction identities therefore imply

    psi_A(v+2m)=-psi_A(v) modulo f,
    psi_A(2m-v)=psi_A(v) modulo f, 0<=v<=m.             (15)

Reduce any nonnegative index ell first modulo2m, then reflect a residue
larger than m. Equations(15) give a sign and an index 0<=r<=m such that

    psi_A(ell)=+/-psi_A(r) modulo f.                    (16)

Because Delta=A^2-1>4 and f^2-Delta*psi_A(m)^2=1,

    0<=psi_A(r)<=psi_A(m)<f/2.                          (17)

This is a uniform statement for all ell; it does not bound or enumerate
the auxiliary index.

Apply it now to N3=1. Since T,U,y are positive and T>1, the ordinary Pell
classification at parameter T gives an index ell>=1 with

    TU=chi_T(ell), y=psi_T(ell).

The index is odd: if ell=2v then `chi_T(ell)=(-1)^v modulo T`, inconsistent
with T dividing TU. Write ell=2v+1. There is an integer polynomial Q_v
satisfying

    chi_T(2v+1)=T*Q_v(T^2),
    Q_0(Z)=1, Q_1(Z)=4Z-3,
    Q_(v+2)(Z)=(4Z-2)Q_(v+1)(Z)-Q_v(Z),
    Q_v(1-A^2)=(-1)^v*psi_A(2v+1).                     (18)

The last identity follows from the same recurrence and initial values;
see [the half-parameter proof, Section3](../../1980/HALF_PARAMETER_PELL_92_PROOF.md).
Equation(7) says T^2=1-A^2 modulo f, so

    U=Q_v(T^2)=(-1)^v*psi_A(ell) modulo f.              (19)

Combining(16)--(19), U has a residue `+/-psi_A(r)` whose absolute value
is strictly less than f/2.

Suppose Nl=-1. Its definition requires U=of-c-2, hence

    U=-c-2 modulo f.                                  (20)

But m>2p by(14), and c=psi_A(p), so

    f>chi_A(2p)=1+2*Delta*c^2>2(c+2).                  (21)

Here A>=3 and c>=3 already suffice for the last inequality; the actual
parameters satisfy much stronger bounds. Both `+/-psi_A(r)` and `-c-2`
lie strictly between -f/2 and f/2. Their congruence must therefore be an
integer equality. It forces psi_A(r)=c+2.

That is impossible: the psi sequence is strictly increasing, and

    psi_A(p+1)-psi_A(p)=(A-1)c+chi_A(p)>2.              (22)

Thus c+2 lies strictly between the consecutive values psi_A(p) and
psi_A(p+1). We conclude **Nl=1**, and restore exactly U=of-c.
Crucially, N3 has used the original root U=jc-R throughout; substituting
of-c into that norm before this argument would change its hypotheses.

## 5. Recovery of90 and positive-witness equivalence

Equations(6) and Nl=1 give Nk*Nt=1, while (7) and Nl=1 restore both
auxiliary comparisons retained in90. Thus every positive zero of P89
satisfies exactly the three90 equations

    T^2=Delta*(f^2-1), U=of-c,
    N0*N1*N2*N3*Nk*Nt=1.                              (23)

Only now invoke [90, Sections4–5](complete75_norm_product90.md): its
negative-index argument forces Nk=Nt=1, and its transport restoration
then gives zplus>=2. Setting z_old=zplus-1 restores a strictly positive
old quotient, and the99/101 theorems restore all earlier eliminated
positive witnesses for this same ordinary input x.

Conversely every positive solution of90 has all six old factors equal1
and both auxiliary residuals zero. Hence N4=Nl=1 and P89=0 on the same
nineteen coordinates. The89 and90 positive solution sets are identical.
Their common inverse map to91 changes only z_old=zplus-1, while the
canonical completeness and dummy-alignment margins of99 remain intact.
No new restriction on the fixed program numerals or the input is imposed.

The dependency order is therefore

    integer product units
    -> four norms and N4 equal1
    -> weak transport C>=0 and packing interval
    -> Nk=+/-1 gives large main index and strong auxiliary rank
    -> folded residues exclude Nl=-1
    -> the90 negative-index proof excludes Nk=Nt=-1
    -> positive old quotient and complete compiler soundness.

Neither positivity of W or mu nor an input-power conclusion is used to
justify an earlier step.

## 6. Literal DAG, exact residual identity, and cost

The [source](complete75_norm_product89.py) and
[receipt](complete75_norm_product89.json) contain the full binary-operation
DAG. All82 certificate gates from90 are retained unchanged, including the
original registers U=`H17`, T^2=`ic22`, `R16=Delta*(f^2-1)`, and
`aux_u_rhs=of-c`. Append exactly

    strong_difference=ic22-R16,
    norm_strong=strong_difference+1,
    linear_difference=H17-aux_u_rhs,
    norm_linear=linear_difference+1,
    seven_units=all_units*norm_strong,
    eight_units=seven_units*norm_linear.               (24)

The single certificate comparison is `eight_units=1`. Its cost is

    82+4A+2M=88=48M+40A.

Append just `polynomial=eight_units-1` to obtain89=48M+41A. Multiplication
by fixed numerals is charged just as in the earlier sources. There are
no remaining external comparisons, inequality tests, powers, divisions,
or sign predicates. A signed output is allowed for a Diophantine equation;
squaring its only residual would add an unnecessary operation and double
the degree.

For a direct identity with the original nineteen-equation source, restore
its deleted coordinates from(1): q,C,k,a,c,d_old=D,kappa,mu,W,r_old=R,
phi=c-kappa, and ga=rho+sigma. Use `alpha_old=alpha+F+Z` and
`z_old=zplus-1`. Write its original literal residuals, indexed from zero,
as r_i. The circuit computes the polynomial identity

    P89=(1-r5)(1+r11)(1+r17)(1+r13)
            *(1+r8)(1+r2)(1+r12)(1+r14)-1.             (25)

The eight factors match N0,N1,N2,N3,Nk,Nt,N4,Nl in that order; all deleted
residuals vanish identically under these substitutions. This is an exact
identity on arbitrary integer assignments, including z_old=0 and signed
computed quantities. Equivalence of positive zero sets is supplied by
Sections2–5, not by the identity alone.

## 7. Exact total degree

Give x and all nineteen supplied coordinates degree one; fixed compiler
numerals have degree zero. Write Q=(B-1)J, k_top=eta+zeta,
gamma_top=rho+sigma and

    C_top=Q-F-Z-alpha-2d*x.

The exact highest homogeneous forms of the eight factors are

| Factor | Degree | Highest homogeneous form |
|---|---:|---|
| N0 |26| `-k_top^2*w^2*s^4*Q^18` |
| N1 |22| `8*gamma_top*k_top*w^2*s^3*Q^15` |
| N2 |42| `-4*delta^2*w^5*s^5*Q^30` |
| N3 |34| `i^2*j^2*k_top^6*s^6*Q^18` |
| Nk |9| `-h*w*s*Q^6` |
| Nt |5| `w*Q^3*C_top` |
| N4 |22| `i^2*k_top^4*s^4*Q^12` |
| Nl |6| `j*k_top*s*Q^3` |

The first six were established in91/90. For N4, T has degree11, while
Delta*(f^2-1) has degree18, so T^2 supplies its highest part. For Nl,
jc has degree6, whereas R has degree4, of degree2, and c degree5.
Every highest form is nonzero. In particular C_top has F coefficient-1
for every admissible B. Their product is therefore nonzero and equals

    -32*(B-1)^105*h*(rho+sigma)*delta^2*i^4*j^3
       *(eta+zeta)^14*w^11*s^24*J^105*C_top.             (26)

The eight degrees sum to166, which is the exact degree of P89. The final
subtraction of1 does not affect that highest part.

## 8. Verification and limits

Default execution regenerates and compares the adjacent receipt:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_norm_product89.py

The checker audits register availability, all literal arithmetic counts,
and512 identities against both independently written eight-factor formulas
and the original nineteen residuals in(25). These include384 positive and
128 signed supplied assignments, across bases16,32,64,256. Signed assignments
check polynomial identities only; the universality theorem has the stated
positive existential domain. Four weighted, offset univariate evaluations
check every factor degree and highest coefficient, and the full degree166
coefficient in(26).

Supporting exact checks cover all64 residue assignments for the N4 modulo4
lemma,15,625 signed integer triples,29,184 folded Pell residues,2,496 odd-index
polynomial identities, and368 strict-gap fixtures. The checker also replays
the signed negative-norm identities, weak-transport and negative-index
fixtures, and actual compiler-margin checks from the preceding packets.
These finite checks supplement the parametric proof. They do not replace
the rank argument or construct the enormous full auxiliary witness towers.

Independent preliminary proof review verified the acyclic dependency order
and the conditional linear-unit exclusion. Separate direct audits checked
64,260 folded-residue cases,3,094 negative-linear gap cases, and all64 modular
assignments. An independent source review replayed512 original-residual
identities, including four negative computed mu values and173 zero restored
old quotients, and independently confirmed89=48M+41A. Three separately
constructed weighted, offset degree checks agreed with(26). A second
independent source audit checked another512 original-residual identities at
bases16,32,128,512, including five deliberately negative computed mu values
with all supplied coordinates positive and192 zero restored old quotients.
It confirmed the full histogram and the degree166 leading form using a
weighted, offset specialization at B=128,d=7. Both independent reviewers
then passed the final proof text, source and default receipt without findings,
including the two-sign bootstrap, rank hypotheses before the linear-unit
recovery, unique signed-residue argument,90 restoration, and exact degree.
The first reviewer additionally checked25,536 residues by independent
quadratic-ring exponentiation and770 strict-gap parameter pairs.

This is an explicit upper bound for this fixed universal compiler. It makes
no claim of global circuit optimality, real-zero equivalence, lower degree
at the same cost, or proof-assistant formalization.
