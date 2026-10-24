# Normalized strong coordinates and integer norm compression

Research note for the parent agent. This note proves the new reductions relative
to the exact unrestricted-integer kernel in the incoming Joint_Guards packet.
It does not claim a new proof of the upstream native/compiler calibration.

## 1. Exact inherited interface

Use the source34 tuple and source71 determinant constants throughout:

    beta = 2^1064921 - 1,
    K0, MC, MF = the complete source34 native ports (MF already shifted),
    Acone = 2^1113, Bcone = 2^666104.

The incoming `joint19_degree88.json` is the immediate unrestricted-integer
parent, with its `joint/PROOF.md` and `guards/PROOF.md` as proof interfaces.
It uses q=beta(3J3+1)+1 and X=4q(3w3+1). This is the already justified
residue-oriented source; no assumption X=2u^2 is silently dropped here.

Write its uncentered first root as tau. Its relevant kernel is

    C = q-F-alpha,
    X = 4q(3w+1), Y=(2v+1)q^3, E=XY, a=(X+1)Y,
    H=4a+3, Delta=a^2+4a+3,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)Jold,
    k=R+1+hE, eta=c-Yk, zeta=k-eta,
    ell=XY^2 k,
    D=X+ac+H gamma,
    G=(Acone F)(Bcone C)-(q-Acone F-Bcone C)^2.

The arithmetic equations are the two main Pell equations

    tau^2=ell(ell+k)+1,
    D^2-Delta c^2=1,

the transport equation

    Btr=(K0+4(3w+1))C-F=z(q-1),

and the ordinary strong and auxiliary relations

    Iold=(2rold+1)c^2,
    Iold^2=Delta(f^2-1),
    Vold+c=f o,
    Vold=jold c-R,
    Iold^2 Vold^2-(Iold^2-1)y^2=1.

The source's centered first root is restored as tau-ell. Its joint guard is

    Jguard = G eta zeta-(t^2-G-eta zeta+1)^2-Pos(p1,p2,p3)=0,
    Pos(p1,p2,p3)=1+p1^2+p2^2+p3(p3+1).

The elementary joint-positivity lemma proves that this row is equivalent,
after existential quantification of t,p1,p2,p3, to G>0 and eta*zeta>0.
For arbitrary values of the four private guard variables, a zero of the
row already implies both strict inequalities. The parent theorem converts
a zero of this kernel into a finite syntactic ZFC refutation.

## 2. Restricting the radix parameter and normalizing the strong ordinate

Supply a new unrestricted integer J and set

    Jold=6J+1, q=beta Jold+1.

This is the parent substitution J3=2J. It makes q even at every integer
assignment, because beta is odd. It does not lose canonical witnesses:
the canonical repunit Jold=1+B+...+B^(N-1) is odd and is 1 modulo 3,
since B=2^1064921 is -1 modulo 3 and the canonical N is odd. Therefore
(Jold-1)/6 is an integer. No claim is made that every arbitrary parent
witness satisfies this extra condition.

Let i=2r+1 and introduce the polynomial registers

    Df = 1+Delta*i^2*c^4,
    Q  = Delta*(Df-1) = Delta^2*i^2*c^4,
    delta = Q-1,
    V = Df*(c*T-R)-c,
    Dt = 1+ell(ell+k),
    Dm = 1+Delta*c^2,
    Cy = Q*V^2-1.

In the proof Dy denotes Cy/delta; it is not an evaluated division in the
polynomial. A recovered integer f with f^2=Df restores the old strong
coordinate by

    Iold=Delta*i*c^2,
    rold=(Delta*i-1)/2.

Indeed a is even, so Delta is odd and rold is an integer. Then
Iold=(2rold+1)c^2 and Iold^2=Delta(f^2-1).

The two old auxiliary quotient variables are restored by integer polynomials:

    o = f*(c*T-R),
    jold = Df*T-1-R*Delta*i^2*c^3.

One checks exactly that jold*c=V+R and f*o=V+c. These identities use
Df-1=Delta*i^2*c^4, which is a polynomial definition, not an inferred
divisibility claim. Thus this step has no circular rank-recovery premise.

## 3. Signed magnitude bounds, before any Pell or native decoding

Only Jguard=0 is used in this section. In particular, no recovered Pell
index, sign of q, or consistency assumption is used.

Put x=|X|, m=|Y|, K=|k|, and Cabs=|c|. The fixed beta and the new integer
parameterization imply |q|>=16. The factors 3w+1 and 2v+1 never vanish,
so x>=64 and m>=4096. Since eta*zeta>0, K>=2 and theta=eta/k lies strictly
between zero and one. Hence c=k(Y+theta) and

    K(m-1) < Cabs < K(m+1).

In particular c is nonzero and Cabs>=2. Write aa=|a|. Then
aa>= (x-1)m, so Delta=(a+2)^2-1>0 and

    sqrt(Delta) > |a+2|-1 >= aa-3 >= (x-1)m-3 > xm/2.

Also sqrt(Delta)>3. Therefore fplus=sqrt(Df) satisfies

    fplus > (xm/2)*Cabs^2 > (xm/2)*K^2*(m-1)^2,
    fplus > 3*Cabs^2.

For tplus=sqrt(Dt), put u=XY^2. Since |u|=xm^2 and k^2=K^2,

    K(xm^2-1) < tplus < K(xm^2+1).

The displayed numerical lower bounds on x,m,K immediately yield

    tplus > 2*Cabs,
    fplus > 2*tplus.

For completeness, the latter comparison follows from
m*K*(m-1)^2/2 > 2*(m^2+1/x), valid already for m>=4,K>=2,x>=1.
Thus the much stronger actual bounds provide ample slack.

These estimates imply Q>Df>Dt>1 and Q>Cabs^2. For b=c*T-R, either
b=0 and |V|=Cabs>1, or

    |V| >= Df-Cabs = fplus^2-Cabs > 2*fplus > 1.

It follows that

    Dy=V^2+(V^2-1)/(Q-1)>V^2>1.

Let yplus=sqrt(Dy). If b=0, then Cabs<yplus<Cabs+1; if b!=0, then
yplus>2*fplus. Consequently the three roots have a strictly
superincreasing order:

    b=0:   fplus > tplus+yplus,   tplus>yplus;
    b!=0:  yplus > fplus+tplus,   fplus>tplus.

For the four-root extension define dplus=sqrt(Dm). Since

    dplus < (aa+3)*Cabs,
    |H| >= 4aa-3,

and aa>5, we get dplus/|H|<Cabs/2. Hence the four positive magnitudes also
admit a strictly superincreasing order:

    b=0:   fplus, tplus, yplus, dplus/|H|;
    b!=0:  yplus, fplus, tplus, dplus/|H|.

Each entry exceeds the sum of all later entries. For example, when b=0,
yplus+dplus/|H|<3*Cabs/2+1<=2*Cabs<tplus, and fplus>2*tplus.
When b!=0, tplus+dplus/|H|<2*tplus<fplus and yplus>2*fplus.

## 4. Radical extraction without an independence assumption

Lemma. Suppose finitely many positive numbers r_j have rational squares,
their magnitudes admit a strictly superincreasing order, and a signed sum
of them is rational. Then every r_j is rational.

Proof. Write each r_j as a positive rational multiple of the square root
of a squarefree positive integer. Distinct squarefree radicals, including
1, are linearly independent over Q. This follows, for example, by the
character projections of the Galois group of the multiquadratic field
generated by the finitely many prime square roots involved. This argument
does not assume that the original radicands have independent square classes.
For any nontrivial square class, its terms must sum to zero separately.
That would be a nonempty signed subsum of the r_j. Its largest magnitude
exceeds the sum of all others, a contradiction. Thus only the trivial
square class occurs.

Apply this lemma to the three or four magnitudes in Section 3. Rational
roots of Dt,Df,Dm are integers because these radicands are integers.
The auxiliary root is integral by the following descent.

## 5. Adjacent-coefficient rational Pell descent

Lemma. For Q>1 integer, V integer and y rational,

    Q V^2-(Q-1)y^2=1

implies y is an integer.

Proof. Take absolute values and write y=a/d in lowest terms, d>0.
The equation gives d^2|(Q-1). If |V|=1 then |y|=1. Otherwise use

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV.

The new V' is integral, the norm is unchanged, and the reduced denominator
of y' is still d because 2Q-1=1 modulo d. From y>|V| and
Q|V|>(Q-1)|y| one gets -|V|<V'<|V|. The norm excludes V'=0.
Induction on |V| reaches |V|=1 without changing d, proving d=1.

This is the existing source69 lemma, applied after the signed bounds have
established Q>1. There is no extrapolation to an arbitrary Pell conic.

## 6. A literal polynomial for the cleared three-root norm

For integer scale s and integer center Z define

    A=s^2*Dt, B=s^2*Df, Cnum=s^2*Cy,
    Jn=delta*(Z^2-A-B)-Cnum,
    Tn=delta^2*A*B, Rn=delta*Cnum,
    Kn=Jn^2-4*(Tn+Rn*(A+B)),
    N3=Kn^2-64*Tn*Rn*Z^2.

Every operation is polynomial. It satisfies the exact identity

    N3 = delta^4 * product over signs e1,e2,e3 of
         (Z-e1*s*sqrt(Dt)-e2*s*sqrt(Df)-e3*s*sqrt(Dy)).

At a joint-guard zero, delta>0 and s!=0 in all proposed uses, so N3=0
gives a signed rational sum and Section 4 applies.

### Sixteen unrestricted integers

The coordinates are J,F,alpha,z,h,r,v,w,gamma,T,c,n,t,p1,p2,p3.
Use s=1,Z=n and let

    Mmain=(X+ac+H gamma)^2-Delta*c^2-1,
    Mtr=Btr-z(q-1),
    S=Mmain^2+Mtr^2+Jguard^2,
    P16=S+N3+S*N3.

Since S>=0, P16=0 is exactly S=N3=0: the integer factor 1+S is positive
and (1+S)(1+N3)=1 forces both factors to be 1. Section 2 reconstructs
the parent variables after extracting the integer roots.

### Fifteen unrestricted integers by absorbing the transport quotient

Delete z from that coordinate list. Set s=q-1, which is nonzero, and
Z=s*n-Btr. Define S=Mmain^2+Jguard^2 and P15=S+N3+S*N3.
At a zero, the radical relation divided by s is

    n-Btr/s = signed tau + signed f + signed y.

All three roots are integers, so Btr/s is an integer. Define z=Btr/s.
The parent transport row is restored. Conversely, from canonical roots
and the parent z, set n=z+tau+f+y. This gives a zero of N3.

Any integral polynomial translation of n is reversible. For example
n->n+V gives the centered formula Jn=delta*(n^2+2nV-Dt-Df)-V^2+1 in
the s=1 case. More elaborate centered variants require their own literal
identity check but do not change this existence proof.

## 7. Fourteen integers through exact transport parametrization and a fourth root

There is also a direct, entirely polynomial way to remove one transport
coordinate. Supply C and z, and set W=4(3w+1), q=beta(6J+1)+1, and

    F=(K0+W)*C-z*(q-1),
    alpha=q-(K0+W+1)*C+z*(q-1).

Then C=q-F-alpha and (K0+W)C-F-z(q-1)=0 identically. Conversely every
old transport zero is restored by these formulas with its original C,z.
This replaces the three variables F,alpha,z subject to one equation by
the two unrestricted variables C,z. It is a unimodular change followed
by a monic elimination, not a divisibility or coprimality assertion.

Use these restored F,alpha everywhere in R and G. The remaining fourteen
coordinates are exactly

    J,C,z,h,r,v,w,T,c,n,t,p1,p2,p3.

Let b0=X+ac. Define F16(Z;A1,A2,A3,A4) as the product of the sixteen
linear factors Z-sum(e_j sqrt(Aj)). Its invariance under every formal
sign flip makes it an integer polynomial in Z,A1,A2,A3,A4. The fourth-root
norm is the ordinary integer polynomial

    N4 = delta^8 * F16(H*n+b0;
                      H^2*Dt,H^2*Df,H^2*Dy,Dm).

The displayed division in Dy is removed by multiplying by delta^8;
no unknown exponent or unexpanded Diophantine predicate is introduced.
A literal recurrence/resultant evaluator should be supplied with the
final packet. Let S=Jguard^2 and P14=S+N4+S*N4.

At a zero, the four-root relation divided by H gives

    n+b0/H = signed tau + signed f + signed y + signed d/H.

Section 3 proves superincreasing magnitudes, so Section 4 gives rational
roots, hence integer tau,f,d and (by descent) integer y. Rearranging
shows

    gamma=(d-b0)/H = n-tau-f-y is an integer.

This restores the parent's main root D=d and its main norm equation.
The other parent variables are restored as before. There is only one
congruence carrier here, with modulus H. The transport equation was
solved polynomially in advance, so no unproved gcd(H,q-1)=1 is used.
Conversely, from canonical parent data after strong normalization, choose
n=gamma+tau+f+y. The norm vanishes. Integer translations of n, such as
n->n+V, are again allowed without any positivity constraint on n.

## 8. Canonical odd normalized strong witness and auxiliary completeness

Let the inherited canonical solution have A=a+2 even, R=3 modulo 4,
c=psi_A(R)>0, and D=chi_A(R). Then c is odd. Put

    I=psi_A(R*c), f=chi_A(R*c).

The composition identity gives I=c*psi_D(c). Since
D^2-1=Delta*c^2, the binomial expansion of the Pell power gives

    psi_D(c) = c D^(c-1) modulo c^2.

Thus c^2 divides I. The recurrence modulo 2 gives psi_A(n)=n modulo 2
when A is even. Since R*c is odd, I is odd; dividing by the odd c^2 gives
an odd positive i=I/c^2. Take r=(i-1)/2. Then f^2=1+Delta*i^2*c^4=Df.
The ordinary strong quotient Delta*i is odd, as required by the parent.

The positive auxiliary reconstruction lemma in source61, label
`lem:auxcomplete`, applies to these fresh f,I. Its hypotheses are
R>=3, R=3 modulo 4, c=psi_A(R), f^2-Delta I^2=1, f,I>0, and c|I.
It supplies positive T,u with V=f^2(cT-R)-c and

    Q V^2-(Q-1)(V+u)^2=1,
    Q=(Delta I)^2=Delta^2*i^2*c^4.

Take y=V+u. This proves completeness without asserting that an arbitrary
old auxiliary quotient is divisible by f. All other arithmetic and native
variables are retained, including the coefficient tuple and residue-oriented
X parameter. The joint guard is unchanged as a predicate in these retained
variables, so its four private witnesses may be retained or regenerated.

Consequently each new equation has an integer zero exactly when the
inherited calibrated kernel does. Composing with that kernel's theorem gives
the ordinary ZFC-formalizable biconditional between no integer zero and
Con(ZFC). This is not an assertion that an actual encoded object-ZFC proof
or a new end-to-end Lean/Rocq artifact has been produced.

## 9. Optional generic monic combiner (possible thirteen-variable extension)

For a finite collection of monic integer polynomials of degree at most four,
let a positive integer R bound the absolute values of all their complex
roots. Any two distinct roots of the same polynomial are separated by at
least (2R)^(-5). To prove this, take its squarefree part, which is still
monic with integer coefficients. Its nonzero discriminant is an integer,
and all root differences are at most 2R. There are at most six pairs, so
isolating the smallest pair in the product of squared differences gives
the stated bound. Repeated roots cause no problem because the squarefree
part is used.

Set M=2+(2R)^6. If r_j are chosen roots, then a rational weighted sum
sum(M^j r_j) forces each r_j rational. For any automorphism of their
splitting field, choose the largest changed index. Its term has modulus
at least M^j(2R)^(-5), while all earlier differences have total modulus
strictly below 2R M^j/(M-1), a contradiction. Every rational root of a
monic integer polynomial is integral. Thus the root-combiner conclusion
holds even when initial chosen roots are complex.

This can combine the joint-guard quartic

    p_t(t)=(t^2-G-eta*zeta+1)^2-G*eta*zeta+Pos(p1,p2,p3)

with square-root polynomials for Dt,Df,Dm and Aaux=delta*Cy. Choose a
polynomial integer majorant R=2+the sum of squares of all nonleading
coefficients; the Cauchy bound gives the required root bound. Put the
main root first with coefficient one and the other four roots with
coefficients H*M,H*M^2,H*M^3,H*M^4. The same argument works because
|H|>=1: for the earliest non-main changed term, all earlier terms have
total normalized weight no larger than the geometric-series bound.
An integer center H*n+b0 then restores gamma after all roots are known
integral. An integer guard root t forces eta*zeta>0, and hence c!=0,Q>1;
the auxiliary square Aaux gives rational y=sqrt(Aaux)/delta, then the
adjacent-coefficient descent makes y integral.

This would leave thirteen unrestricted coordinates
J,C,z,h,r,v,w,T,c,n,p1,p2,p3 and one degree-64 root-combiner polynomial.
It is a proposal until its exact norm evaluator, degree, cost, source binding,
and exceptional-specialization checks have been generated and audited.
The generic monic-combiner technique itself is not claimed novel.

## 10. Preferred thirteen-integer equation: five square tests and one norm

This improves the optional preceding proposal: eliminate the private
square variable p1, retaining t, rather than eliminating the quartic variable
t. All five root conditions are then square conditions. The final norm has
degree32 in its center, and total degree3744 under the supplied weight plan.

The thirteen unrestricted integer coordinates are exactly

    J,C,z,h,r,v,w,T,c,n,t,p2,p3.

Use the transport parametrization of Section7, and all its definitions of
q,X,Y,E,a,H,Delta,F,alpha,R,k,eta,zeta,G,Df,Q,delta,V,Dt,Dm,Cy. Define

    A0=Dm,
    A1=Df,
    A2=Dt,
    A3=G*eta*zeta-(t^2-G-eta*zeta+1)^2
       -1-p2^2-p3*(p3+1),
    A4=delta*Cy.

The degree upper bounds, on the fully substituted polynomials, are

    d0=14, d1=18, d2=34, d3=44, d4=106.

Let Li>=0 be explicit fixed integer bounds on the sums of absolute values
of the numerical coefficients of Ai for i=0,1,2,3. They can be obtained
without expansion by the following sound syntactic coefficient-norm rules:
constants have bound their absolute value, a variable has bound1, addition
and subtraction add bounds, and multiplication multiplies bounds. These
rules use the actual fixed coefficient ports. Hence each Li is a particular
computable integer numeral, not a free parameter.

Set

    rho=1+J^2+C^2+z^2+h^2+r^2+v^2+w^2+c^2+t^2+p2^2+p3^2,
    B0=(L0+1)*rho^4,
    B1=(L1+1)*rho^5,
    B2=(L2+1)*rho^9,
    B3=(L3+1)*rho^11,
    w0=1,
    w1=H*(1+B0),
    w2=w1*(1+B1),
    w3=w2*(1+B2),
    w4=w3*(1+B3),
    Z=H*n+X+a*c.

The carrier n MUST NOT occur in rho. Otherwise the canonical choice of n
below would be circular. The coordinate T need not occur either, since
none of A0,A1,A2,A3 contains T. All weights are therefore determined before
n is selected. Each wi is a nonzero integer and, for i>=1, is divisible
by H. The weights for i>=1 share the sign of H. H never vanishes because H=4a+3.

The literal polynomial is

    P13 = product over all32 sign vectors epsilon in {+1,-1}^5 of
          (Z-sum_i epsilon_i*w_i*sqrt(Ai)).

This display specifies an ordinary integer polynomial: flipping one formal
square root permutes the factors, so every formal root appears only to even
powers after expansion. A recurrence evaluator can construct it solely by
integer polynomial arithmetic; no square root is evaluated in the final
Diophantine equation. The square-root product is a compact definition of
that fixed polynomial.

### 10.1 Unconditional square extraction

For i<=3 and any integer assignment, every variable occurring in Ai has
absolute value at most sqrt(rho). Thus

    |Ai| <= Li*rho^(di/2),
    |sqrt(Ai)| <= sqrt(Li)*rho^(di/4) < Bi.

This bound remains true for complex roots of negative Ai, using their
complex moduli. A nonzero square root of an integer has modulus at least1.

The weight recurrence gives the strict bound

    sum_{i<j} |wi|*Bi < |wj|      for 1<=j<=4.

Indeed |w1|-B0=|H|+(|H|-1)B0>0, while
|wi|*Bi=|w_(i+1)|-|wi| for i>=1.
No bound on A4 is needed: it is placed last and its nonzero roots have
modulus at least1.

If P13=0, one complex linear factor vanishes, so Z is a signed weighted
sum of square roots of the Ai. Group these terms by nonzero rational
square classes. The distinct classes, including negative square classes,
are linearly independent over Q in their multiquadratic field. In any
nontrivial class, choose its largest participating index j. Its nonzero
term has modulus at least |wj|, while every earlier term in that class
together has modulus strictly less than |wj|. They cannot sum to zero.
Therefore no nontrivial square class occurs: all five Ai are nonnegative
integer squares. Zero radicands contribute nothing and cause no exception.

This proof establishes the guard square before using any positivity
consequence of the guard. In particular it avoids circular use of the
signed bounds from Section3. Those bounds are needed for the low-degree
four-root companion, but not for this five-square construction.

### 10.2 Recovering all parent witnesses

Choose the signed integer roots furnished by the vanishing factor and
write them as d,f,tau,p1,baux, respectively. Since A3=p1^2, its defining
identity is exactly Jguard=0 with the restored private coordinate p1.
Hence G>0 and eta*zeta>0.

The latter strict inequality excludes c=0: if c=0 then
eta=-Yk,zeta=(Y+1)k and eta*zeta=-Y(Y+1)k^2<=0, since Y is an integer.
Unconditionally Delta is positive and odd, and i=2r+1 is nonzero. Thus
at a zero, Q=Delta^2*i^2*c^4>1 and delta>0. In fact delta cannot vanish
at any integer assignment: if c=0 then Q=0, while if c!=0 then Q>1.

The auxiliary square baux^2=delta*(QV^2-1) gives the rational number
y=baux/delta satisfying QV^2-(Q-1)y^2=1. Section5 makes y an integer.
The other square tests give f^2=Df, tau^2=Dt, and d^2=Dm.

In the weighted root relation, every term except d is divisible by H.
Therefore d=Z modulo H and

    gamma=(d-X-ac)/H
         =n-sum_{i=1}^4 (wi/H)*root_i

is an integer. Here wi/H is an explicit integer product, so no
unproved divisibility assumption is present. This restores the main Pell
root with its required congruence. Section2 supplies rold,o,jold and the
ordinary strong and auxiliary equations. The transport equations hold
identically by Section7. Thus every P13 zero yields a zero of the exact
calibrated integer parent.

### 10.3 Completeness and quantifier order

Begin with a canonical refutation witness of the inherited parent.
Use J=(Jold-1)/6 and the transport parametrization, and regenerate the
odd normalized strong and auxiliary witnesses by Section8. Retain or
regenerate t,p1,p2,p3 for the same native and eta*zeta guards. All
thirteen coordinates except n are now fixed; the five square roots are
d,f,tau,p1,delta*y, and every weight is already fixed as well.

Define

    n=gamma+sum_{i=1}^4 (wi/H)*root_i.

This is an integer, with no sign requirement. Since d=X+ac+H gamma,
the chosen factor of P13 vanishes. This completes the two-way existence
equivalence and hence the inherited Con(ZFC) calibration.

### 10.4 Exact degree3744

The weighted radicands wi^2 Ai have degree upper bounds

    14,46,82,128,234,

and Z has degree7. In the32-factor norm, the unique possible contribution
at total degree16*234=3744 is (w4^2 A4)^16, with coefficient1. Every
replacement by another radicand or by Z strictly lowers total degree.

For an explicit nonzero leading form, put

    q0=6 beta J, W0=12w, Y0=2v q0^3,
    a0=W0 q0 Y0, i0=2r,
    F0=W0 C-q0 z, R0=-q0^3 F0,
    rho0=J^2+C^2+z^2+h^2+r^2+v^2+w^2+c^2+t^2+p2^2+p3^2,
    Kbound=(L0+1)(L1+1)(L2+1)(L3+1).

Then the degree234 part of w4^2 A4 is

    16*Kbound^2*a0^14*i0^8*c^16*R0^2*rho0^58.

It is a nonzero polynomial for the actual beta>0 and Li>=0. Consequently
the degree3744 part of P13 is exactly its sixteenth power, proving the
claimed degree without an inference from uncancelled gate degrees alone.

The innovation relative to the audited incoming family is this complete
composition: exact transport coordinates, odd normalized strong witnesses,
auxiliary rational descent, absorption of the main congruence, and a
degree-conscious five-square norm. The generic square-combiner principle,
the individual positivity lemma, and adjacent-coefficient descent are
inherited techniques, not claimed as new general theorems.

## 11. Preferred final improvement: the unweighted thirteen-integer norm

This section supersedes the weighted Section10 endpoint. It removes every
coefficient majorant Li and every separating weight, keeps the original six
fixed coefficient ports, and lowers the exact total degree to1408. The key
is a noncircular sign bootstrap: the guard radical is the only one that
could be imaginary, and once it is real its magnitude is automatically
small enough for the existing Pell roots to separate it.

Use exactly the thirteen coordinates of Section10 and its source
definitions and transport parametrization. Let

    Ag=G*eta*zeta-(t^2-G-eta*zeta+1)^2
       -1-p2^2-p3*(p3+1),
    b0=X+a*c,
    Z=H*n+b0.

For a center Z and five radicands let F32 be the product of the32 formal
conjugate linear factors. The final polynomial is

    P13_unweighted = delta^16 *
        F32(Z; Dm, H^2*Df, H^2*Dt, H^2*Ag, H^2*Cy/delta).

Its polynomiality is immediate because the degree of F32 in each
radicand is at most16. Every apparent denominator is cleared by delta^16.
The literal evaluator must use the cleared polynomial recurrence, never
a numerical square-root or division oracle.

### 11.1 All non-guard roots are real before any source decoding

The parameterization alone gives q even and nonzero, X nonzero, Y nonzero,
|X|>=64, |Y|>=4096, and |a|>18. Thus Delta>0, H!=0, and the radicands
Dm,Df are at least1. Also Dt=1+k^2*u*(u+1)>=1 for the integer u=XY^2,
because u(u+1)>=0. No guard or Pell equation is used here.

If c=0, then Q=0, delta=-1, Cy=-1, and Dy=Cy/delta=1. If c!=0,
then Q=Delta^2*i^2*c^4>1 and Df=1+Delta*i^2*c^4>|c|+1. For the
integer b=c*T-R, V=Df*b-c has |V|>=1: b=0 gives |V|=|c|, while
b!=0 gives |V|>=Df-|c|>1. Consequently

    Dy=V^2+(V^2-1)/(Q-1)>=1.

This proves two facts on every integer assignment: delta never vanishes,
and Dm,Df,Dt,Dy are positive. It explicitly covers the c=0 branch.

### 11.2 A real root first recovers the strict guards

At a zero of P13_unweighted, delta!=0, so one formal conjugate factor
of F32 vanishes over C. The center Z is real, and four radicals are real
by Section11.1. If Ag<0, the fifth radical is the nonzero imaginary number
H*sqrt(Ag), up to sign; it cannot cancel the other real terms. Therefore
Ag>=0 at every polynomial zero.

By definition,

    Pair(G,eta*zeta,t)
      = Ag + 1+p2^2+p3*(p3+1) > 0.

The elementary joint-positivity lemma therefore gives G>0 and eta*zeta>0
BEFORE any assertion that Ag is a square. It follows in particular that
c!=0, hence Q>1 and delta>0. This is the crucial proof order: realness
gives the guards, the guards give magnitude separation, and separation
then gives rationality and integrality of every root.

### 11.3 The determinant bounds the new guard radical

Write U=Acone*F and Wcone=Bcone*C. Since

    G=U*Wcone-(q-U-Wcone)^2>0,

U and Wcone have the same nonzero sign and

    |q-U-Wcone|<sqrt(U*Wcone)<=(|U|+|Wcone|)/2.

Hence |U|+|Wcone|<2|q|, and

    0<G<U*Wcone<=((|U|+|Wcone|)/2)^2<q^2.

This bound is independent of the enormous sizes of the two fixed cone
coefficients; it is a consequence of the determinant itself.

Let gplus=sqrt(Ag), possibly zero, and keep K=|k|, Cabs=|c|, m=|Y|.
Since eta*zeta<=k^2/4 and the subtracted Pos2 is strictly positive,

    gplus < |q|*K/2.

But Cabs>K(m-1), m>=|q|^3, and |q|>=16, so

    gplus<Cabs/10.

The main root satisfies the sharper two-sided estimate

    Cabs/5 < dplus/|H| < Cabs/2.

The upper bound was proved in Section3. For the lower bound use
sqrt(Delta)>|a|-3 and |H|<=4|a|+3: because |a|>18,
(|a|-3)/(4|a|+3)>1/5. Thus dplus/|H|>2*gplus.

### 11.4 Five-root separation and witness reconstruction

Section3 already proved tplus>2*Cabs, fplus>2*tplus, and the two cases
for yplus. They now show strict superincreasing order for all five roots:

    b=0:   fplus, tplus, yplus, dplus/|H|, gplus;
    b!=0:  yplus, fplus, tplus, dplus/|H|, gplus.

Zero gplus is simply omitted. In the b=0 case,
yplus+dplus/|H|+gplus < 1.6*Cabs+1 < 2*Cabs < tplus,
and yplus>Cabs>dplus/|H|+gplus. In the b!=0 case,
dplus/|H|+gplus<0.6*Cabs<tplus, and yplus>2*fplus.
The other inequalities follow from fplus>2*tplus and the lower bound
dplus/|H|>2*gplus.

Divide the vanishing factor by H. It expresses the rational number
n+b0/H as a signed sum of these five positive rational-square roots.
The square-class lemma in Section4 therefore makes all five roots
rational. The roots of the integer radicands Dm,Df,Dt,Ag are integral;
the rational auxiliary root is integral by Section5.

Let the signed roots in the actual factor be d,f,tau,p1,y. Then

    H*n+b0=d+H*(f+tau+p1+y),
    gamma=n-f-tau-p1-y=(d-b0)/H is an integer.

The guard root p1 restores Jguard=0. Every parent variable and every
source equation is restored exactly as in Sections2,7,8. Conversely, take
the canonical normalized witnesses and a guard representation, and set

    n=gamma+f+tau+p1+y.

No weight depends on n and no sign condition is imposed on it. The
corresponding factor of the norm vanishes. Thus this single ordinary
polynomial has an integer zero exactly when the calibrated parent does.

### 11.5 Exact degree1408

With the fully substituted thirteen-coordinate definitions,

    deg(delta)=30, deg(H^2*Cy)=88, deg(Z)=7,
    deg(Dm)=14, deg(H^2*Df)=30,
    deg(H^2*Dt)=46, deg(H^2*Ag)=56.

F32 is weighted homogeneous of weight32 when the center has weight1 and
every radicand has weight2. A term using the auxiliary radicand to power j
becomes, after denominator clearing, a term of degree at most

    30*(16-j)+88*j+56*(16-j)=1376+2j.

Here degree56 also bounds each pair of center factors, whose degree is14.
Thus only j=16 can reach1408. The coefficient of the sixteenth power of
any one radicand in the generic norm is+1, so the top part is exactly
(H^2*Cy)_88^16.

Using the q0,W0,Y0,a0,i0,F0,R0 from Section10,

    (H^2*Cy)_88 = 16*a0^10*i0^6*c^12*R0^2.

This is a nonzero polynomial on the actual fixed coefficient slice.
Consequently the degree1408 part of P13_unweighted is precisely

    (16*a0^10*i0^6*c^12*R0^2)^16.

The bound is therefore exact, not merely a gate-degree estimate. This
argument also proves that the equation is not the zero polynomial.

The new bootstrap and separation use the determinant guard's own
quantitative information. No additional coefficient payload or unproved
canonical freedom of Y is needed.

## 12. The centered flagship: exact degree1392

Replace the center in Section11 by

    Z=H*(n+V)+b0, b0=X+a*c.

This is the substitution n_old=n_new+V. Since V is an integer polynomial
in the other twelve supplied coordinates and does not involve n, this
is an affine integer bijection on every fiber. Its inverse is
n_new=n_old-V. All existence equivalences and all signed-root arguments
of Section11 therefore apply verbatim. In particular the canonical new
carrier is gamma+f+tau+p1+y-V. This translation is legitimate over all
integers; no assertion is made about preservation of a positive domain.

The centered polynomial remains

    P13_centered=delta^16*
       F32(Z; Dm,H^2*Df,H^2*Dt,H^2*Ag,H^2*Cy/delta).

Its exact degree is1392, and it has only the same six native/cone fixed
coefficient ports as Section11.

### 12.1 A short exact evaluator and a degree filtration

Work temporarily in the formal commutative algebra generated by u,v
with u^2=d=Dm and v^2=e=H^2*Ag. This is a free module with basis
1,u,v,uv; no claim that a specialized algebra is a field is needed.
Put

    A=H^2*Df, B=H^2*Dt, Cnum=H^2*Cy,
    Xformal=Z+u+v,
    Xformal^2=(Z^2+d+e)+2Z*u+2Z*v+2*u*v,
    J=delta*(Xformal^2-A-B)-Cnum,
    K=J^2-4*(delta^2*A*B+delta*Cnum*(A+B)),
    L=K^2-64*delta^3*A*B*Cnum*Xformal^2.

The element L is exactly the cleared three-root norm N3 evaluated at
Xformal. Taking its conjugate product under u->-u and then v->-v gives
the centered thirteen-variable polynomial. This uses only polynomial
arithmetic and proves the full32-factor norm identity, including
specializations d=0,e=0, negative e, and coincident square classes.

For explicit implementation, squaring (x0,x1,x2,x3) in this algebra gives

    r0=x0^2+d*x1^2+e*x2^2+d*e*x3^2,
    r1=2*(x0*x1+e*x2*x3),
    r2=2*(x0*x2+d*x1*x3),
    r3=2*(x0*x3+x1*x2).

Its norm in u is the pair, on the basis1,v,

    s0=x0^2+e*x2^2-d*(x1^2+e*x3^2),
    s1=2*(x0*x2-d*x1*x3).

The remaining norm is s0^2-e*s1^2. These are exact identities over the
integer polynomial ring.

For degree bookkeeping, assign formal weight7 to u and28 to v, matching
half the exact degrees14 and56 of d and e. A coefficient on the basis
1,u,v,uv is assigned its polynomial degree plus respectively0,7,28,35.
Multiplication respects the resulting degree filtration because replacing
u^2 by d and v^2 by e preserves these degree bounds.

Let s=H*n+b0, whose degree is7. The scalar coefficient of J has the
exact cancellation

    J0=delta*(s^2+2*H*V*s+d+e-A-B)-H^2*(V^2-1).

Indeed Z=s+HV and Cnum=H^2*((delta+1)V^2-1). The term delta*e has
degree86, larger than every other term in J0. The four coefficients of J
therefore have the following weighted degrees and leading information:

    basis1:  J0, degree86, leading Q0*e0;
    basisu:  2delta*Z, weighted degree66;
    basisv:  2delta*Z, weighted degree87;
    basisuv: 2delta, weighted degree65.

The unique highest weighted component is2Q0*Z0*v, of weight87.
Consequently J^2 has a unique leading scalar (2Q0 Z0)^2 e0 of degree174.
The scalar subtrahend in K has degree at most164, so K has this same
leading scalar. The subtrahend in L has weighted degree at most312:
90+30+46+88+58=312. Thus L has unique leading scalar

    L0=16*Q0^4*Z0^4*e0^2, degree348.

Every other weighted component has smaller degree. Taking the two
quadratic norms therefore yields the unique top polynomial L0^4,
of exact degree1392.

### 12.2 Explicit nonzero top form and a selected monomial coefficient

Use the definitions from Section10 and put

    eta0=-h*X0*Y0^2,
    Q0=a0^4*i0^2*c^4,
    V0=-a0^2*i0^2*c^4*R0,
    Z0=4*a0*V0,
    e0=-16*a0^2*eta0^4.

Here X0=q0 W0, Y0=2v q0^3, a0=X0Y0, i0=2r,
q0=6beta J, W0=12w, and R0=-q0^3(W0C-q0z). The leading forms are
all nonzero on the authentic fixed coefficient slice. Substitution gives

    (P13_centered)_1392
      =2^16*Q0^16*Z0^16*e0^8
      =2^80*a0^128*i0^64*c^128*R0^16*eta0^32.

In particular, the coefficient of

    J^800*w^160*v^192*h^32*r^64*c^128*z^16

is exactly

    2^1456 * 3^960 * beta^800 > 0.

To verify it directly, use
a0=2^7*3^5*beta^4*J^4*w*v,
eta0=-2^11*3^8*beta^7*J^7*h*w*v^2,
and the q0^4*z term of R0. The z^16 power selects that term uniquely;
all other leading factors are monomials. The total exponent sum is1392.
This provides an exact numerical-slice degree certificate independent
of K0,MC,MF,Acone,Bcone.

### 12.3 Additional familiar centers do not improve the degree

The usual strong center (a+2)*i*c^2 has degree9, and the first-Pell center
ell=XY^2*k has degree17. If either or both are added to n along with V,
then s=H*(n+these centers)+b0 has degree at most23. In the displayed
formula for J0, the term2delta*H*V*s then has degree at most82, and
delta*s^2 has degree at most76. Both remain below the degree86 term
delta*e. The unique weight87 v-component is unchanged because V still
dominates the center Z. Thus these additional translations leave the
degree1392 leading form unchanged. They add description cost without
improving this degree certificate, and are unnecessary in the flagship.

## 13. A fourteen-integer companion of degree696

The fourteen-variable equation retains the joint guard as a separate
residual, so it can center the remaining four Pell roots more aggressively.
Use the fourteen coordinates of Section7 and put

    I=i*c^2, Fstrong=(a+2)*I, ell=XY^2*k,
    Z=H*(n+2V+2ell+k+2Fstrong)+2b0,
    N4=delta^8*F16(Z;4Dm,4H^2*Df,4H^2*Dt,4H^2*Dy),
    S=Jguard^2,
    P14_centered=S+N4+S*N4.

The degree claim below is exact: N4 has degree608 and the final P14 has
degree696. It uses the same six fixed coefficient ports as the other
constructions.

### 13.1 Existence equivalence with the scaled center

The unit-product finalizer gives S=N4=0. The joint guard therefore makes
the four-root separation proof of Section3 available. Dividing a vanishing
norm factor by2H gives a rational signed sum of d/H,f,tau,y. Consequently
the four roots are rational and then integral, as before.

The norm factor gives Z=2d+2H(f+tau+y). Modulo H it follows that
2d=2b0. Since H=4a+3 is odd,2 is invertible modulo H, so d=b0 modulo H.
The integer gamma=(d-b0)/H restores the main source root. All other
restorations are unchanged. This argument does not assume that n or k
has a particular parity.

For completeness, choose canonical normalized parent roots and set

    n=2gamma+2f+2tau+2y-2V-2ell-k-2Fstrong.

It is an integer, and the corresponding norm factor vanishes. Thus the
scaled center preserves the required existential equivalence. Unlike the
Section12 shear, this is not asserted to be a bijection preserving every
arbitrary old carrier coordinate; the two explicit existence implications
are the proof.

### 13.2 Exact leading degree through formal root expansions

Put

    Uf=2H*Fstrong, Ut=H*(2ell+k), Uy=2H*V,
    Scenter=H*n+2b0.

Then Z=Scenter+Uf+Ut+Uy, and the three scaled Pell radicands have the
exact forms

    4H^2*Df = Uf^2+4H^2*(1-I^2),
    4H^2*Dt = Ut^2+H^2*(4-k^2),
    4H^2*Dy = Uy^2+4H^2*(V^2-1)/delta.

Their center degrees are respectively15,23,29; the correction degrees
are18,26,28 (the last is a rational-function degree). Therefore the
formal roots with the chosen leading signs have deviations from Uf,Ut,Uy
of degrees at most3,3,-1, respectively.

For a precise justification, replace every supplied variable x by t*x and
work over the rational-function coefficient field in the remaining
indeterminates. If deg(E)<2deg(U), the formal Laurent-series branch
sqrt(U^2+E)=U*sqrt(1+E/U^2) differs from U by degree at mostdeg(E)-deg(U).
The binomial series is valid in characteristic zero. The final norm is an
ordinary polynomial, so its highest Laurent exponent in t is its total
degree. This calculation is independent of the signs of specialized
integer witnesses and does not introduce an analytic approximation.

Among the16 conjugate factors, the first sign not agreeing with these
three centered roots determines the leading term:

    eight factors: 2Uy, degree29;
    four further factors: 2Ut, degree23;
    two further factors: 2Uf, degree15;
    final main-root pair: Scenter^2-4Dm, degree14.

For the final pair the root corrections have degree at most3, below the
degree7 of Scenter and the main root. The degree14 leading form is

    (H0*n+2a0*c)^2-4a0^2*c^2
      =H0^2*n*(n+c),  H0=4a0.

Clearing delta^8 adds degree240. Hence the exact degree of N4 is

    8*29+4*23+2*15+14+240 = 608.

The leading form is

    (N4)_608 = 2^28*Q0^8*H0^16*V0^8*ell0^4*
               Fstrong0^2*n*(n+c),

where Fstrong0=a0*i0*c^2 and ell0=h*X0^2*Y0^3. Substituting the
definitions reduces this to

    2^60*a0^66*i0^34*c^68*R0^8*ell0^4*n*(n+c).

It is nonzero. The degree88 part of S=Jguard^2 is eta0^8, so the final
product P14 has exact degree608+88=696, with top form

    (P14_centered)_696=(N4)_608*eta0^8.

The lower summands S and N4 cannot cancel this top degree.

### 13.3 A coefficient certificate

The coefficient of

    J^396*w^82*v^94*h^12*r^34*c^68*z^8*n^2

in P14_centered is exactly

    2^748 * 3^478 * beta^396 > 0.

For the norm alone, the coefficient of
J^340*w^74*v^78*h^4*r^34*c^68*z^8*n^2 is
2^660*3^414*beta^340. Multiplication by eta0^8 adds the remaining
exponents and the factor2^88*3^64*beta^56. These coefficients use the
unique z^8 term of R0^8 and the n^2 term of n(n+c), so no hidden sum
of leading coefficients is involved.

## 14. A coprime carrier lowers the thirteen-integer degree to1088

This variant retains thirteen unrestricted integer coordinates and the
same six fixed native/cone numerals, but changes the supplied scale
coordinate. It removes two explicit powers of q from Y and restores the
missing scale divisibility through a congruence carrier whose moduli are
provably coprime. It does not assume any unproved freedom to choose the
canonical Y.

### 14.1 Complete definitions

The supplied coordinates are

    J,C,z,h,r,v,w,T,c,n,t,p2,p3 in Z.

Use Jold=6J+1, q=beta Jold+1, W=4(3w+1), and

    X=qW, Y=q*v, E=XY, a=(X+1)Y,
    H=4a+3, Delta=a^2+4a+3,
    F=(K0+W)C-z(q-1), alpha=q-F-C,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)Jold,
    k=R+1+hE, eta=c-Yk, zeta=k-eta,
    G=(Acone F)(Bcone C)-(q-Acone F-Bcone C)^2,
    i=2r+1, Df=1+Delta*i^2*c^4,
    Q=Delta*(Df-1), delta=Q-1,
    V=Df*(cT-R)-c, Cy=Q V^2-1,
    Dt=1+XY^2*(XY^2+1)*k^2,
    Dm=1+Delta*c^2,
    Ag=v^2*(G*eta*zeta-(t^2-G-eta*zeta+1)^2)
       -1-p2^2-p3*(p3+1).

The only difference in the raw guard is the new multiplier v^2. It
forces v!=0 and has a controlled effect on the guard-root magnitude.

For the congruence carrier set

    M=2q^2, Lcrt=4H+1, U=M H, b0=X+ac,
    Z=U*(n+V)+M*Lcrt*b0+H*(v-q^2).

The ordinary polynomial is

    P13_CRT=delta^16*F32(
       Z;
       M^2*Lcrt^2*Dm,
       U^2*Df,
       U^2*Dt,
       U^2*Ag,
       U^2*Cy/delta).

All symbols are polynomial abbreviations, not additional variables.
The one displayed division is cleared by delta^16 in the exact norm.
The transport equation is still solved identically by F and alpha.

### 14.2 Unconditional exceptional-case analysis

As before q is even, q=2 modulo3, |q|>=16, and X is nonzero with
|X|>=64. If v=0 then Y=a=0, Delta=3 and H=3. If v!=0 then
|Y|>=16 and |a|>=63*16, so Delta>0 and |H|>3. Therefore Delta is
positive and odd and H is nonzero on every integer assignment. Moreover
3<Lcrt/H<5 (indeed H=3 or |H| is very large), so Lcrt is also nonzero.

For c=0 we have Q=0, delta=-1 and Cy/delta=1. For c!=0,
Q=Delta^2*i^2*c^4>1 and Df>|c|+1. Writing b=cT-R, the expression
V=Df*b-c has |V|>=1, exactly as in Section11. Thus Cy/delta>=1.
The other three non-guard radicands are positive as well. Hence delta
never vanishes and every non-guard radical is real before any source
decoding.

At a polynomial zero, Ag cannot be negative: its radical would be the
only nonzero imaginary summand in a factor with a real center. Therefore

    v^2*Pair(G,eta*zeta,t)
      = Ag+1+p2^2+p3(p3+1)>0.

This proves v!=0 and Pair(G,eta*zeta,t)>0. The joint-positivity lemma
then gives G>0 and eta*zeta>0. In particular c!=0, Q>1, and delta>0.
When v=0 the guard radicand is strictly negative, so that branch is
excluded by realness, not by a circular magnitude argument.

### 14.3 Signed separation with the weaker scale bound

Put x=|X|, mY=|Y|, K=|k|, and Cabs=|c|. The strict guard gives

    x>=64, mY>=|q|>=16, K>=2,
    K(mY-1)<Cabs<K(mY+1).

Thus Cabs>30. The first-Pell root tauplus satisfies

    K(x*mY^2-1)<tauplus<K(x*mY^2+1),
    tauplus>2*Cabs.

Let dplus=sqrt(Dm), fplus=sqrt(Df), yplus=sqrt(Cy/delta),
gplus=sqrt(Ag), and lambda=Lcrt/H. The determinant bound G<q^2
still holds. It gives

    gplus<|v|*|q|*K/2=K*mY/2<8*Cabs/15.

The main root is now deliberately placed ABOVE the first root. Indeed

    dplus > ((x-1)mY-3)*K*(mY-1) > (3/4)*tauplus.

The second inequality follows by expanding

    4*((x-1)mY-3)*(mY-1)-3*(x*mY^2+1)
      =mY^2*(x-4)-4mY*(x+2)+9>0

for x>=64,mY>=16. Since3<lambda<5,

    lambda*dplus>2*tauplus.

Also

    fplus^2>Delta*Cabs^4,
    dplus^2=Delta*Cabs^2+1<2Delta*Cabs^2,

so fplus>(Cabs/2)*dplus>15*dplus>2*lambda*dplus. The old estimate
fplus>3Cabs^2 also remains valid. Thus, for b=cT-R,

    b=0:   Cabs<yplus<Cabs+1;
    b!=0:  yplus>2*fplus.

When b=0,
yplus+gplus<(23/15)Cabs+1<2Cabs<tauplus. The five positive
magnitudes have strict superincreasing order

    fplus, lambda*dplus, tauplus, yplus, gplus.

When b!=0 the order is

    yplus, fplus, lambda*dplus, tauplus, gplus.

Zero gplus is omitted. Dividing a vanishing norm factor by U expresses
a rational number as a signed sum of exactly these magnitudes. The
square-class lemma therefore gives rational d,f,tau,p1,y. The first four
are integers by their integer radicands; y is integral by adjacent-
coefficient descent. No source rank theorem was used to obtain these roots.

### 14.4 The two coprime congruences restore the original scale and main root

Because Y=qv,

    H=4(X+1)qv+3 = 3 modulo q.

The fixed odd exponent1064921 gives beta=1 modulo3, so q=2 modulo3.
Together with H odd this proves

    gcd(H,M)=gcd(H,2q^2)=1.

Also Lcrt=1 modulo H. Let the signed integer roots in the vanishing
factor be d,f,tau,p1,y. Their equation is

    U(n+V)+M Lcrt b0+H(v-q^2)
       =M Lcrt d+U(f+tau+p1+y).

Modulo M it gives H(v-q^2)=0. The proved coprimality implies

    v=q^2*(2vold+1),
    vold=(v-q^2)/(2q^2) in Z.

Therefore Y=qv=(2vold+1)q^3, exactly the old source scale, including
its odd-quotient condition. Modulo H the same equation gives
M Lcrt(d-b0)=0. Cancelling the two units modulo H proves

    gamma=(d-b0)/H in Z.

The main Pell and scale equations of the original parent are therefore
restored. Section2 restores the odd ordinary strong quotient and both
auxiliary quotient variables. The strict native/eta guards already hold;
since Pair(G,eta*zeta,t)>0, the ternary Pos representation supplies the
old private guard variables. They need not equal the new private variables,
which represent v^2*Pair instead. The transport relation holds identically.
This completes soundness relative to the exact same calibrated parent.

### 14.5 Canonical completeness, with the carrier sign fixed

Start with a canonical parent solution, perform the strong normalization
of Section8, and keep all its native quantities. Set the new v to

    v=Yold/q=q^2*(2vold+1).

It is nonzero. Choose t with Pair(G,eta*zeta,t)>0 and then choose new
p1,p2,p3 representing the positive integer v^2*Pair. Thus Ag=p1^2.
The other four radicands are supplied by the canonical Pell roots.

Set

    n=Lcrt*gamma+f+tau+p1+y-V-(v-q^2)/M.

Every term is an integer, and direct substitution gives the vanishing
factor in Section14.4. This is the exact carrier sign convention for
the displayed centered equation. The construction does not change the
canonical Y; it re-encodes its already known divisibility.

The normalized odd strong witness remains justified by recurrence parity:
A=a+2 is even, R and c are odd, so psi_A(Rc) is odd. Dividing it by the
odd c^2 gives an odd i. Its parity is not inferred from only the first
term of a binomial congruence.

### 14.6 Exact degree1088 and an independent coefficient target

For this new scale parameterization the degrees are

    deg(a)=4, deg(Delta)=8, deg(Df)=14, deg(Q)=22,
    deg(R)=5, deg(V)=19, deg(Cy)=60,
    deg(Dt)=22, deg(Ag)=30, deg(U)=6,
    deg(d=M^2 Lcrt^2 Dm)=22,
    deg(e=U^2 Ag)=42,
    deg(A=U^2 Df)=26, deg(B=U^2 Dt)=34,
    deg(Cnum=U^2 Cy)=72, deg(Z)=25.

Use the same cleared three-root evaluator in the biquadratic algebra
u^2=d, vformal^2=e, assigning weights11 and21 to the two formal roots.
Put s=U*n+M Lcrt b0+H(v-q^2), whose degree is11. The scalar J cut is

    J0=delta*(s^2+2U V s+d+e-A-B)-U^2*(V^2-1).

Its degree is64, from delta*e. The four weighted J-component degrees are

    [64,58,68,54].

The unique largest component is2delta Z*vformal, of weight68.
The scalar subtraction in K has degree at most128, below136; the tail
subtraction in the cleared N3 has weight at most248, below272. Hence
the cleared N3 has unique leading scalar16*Q0^4*Z0^4*e0^2 of degree272.
The two quadratic norms give exact degree1088 and leading form

    2^16*Q0^16*Z0^16*e0^8.

For explicit leading polynomials define

    q0=6beta J, W0=12w, Y0=q0*v, X0=q0*W0,
    a0=X0Y0, i0=2r,
    F0=W0C-q0z, R0=-q0^3 F0,
    k0=R0+h*a0, eta0=-Y0*k0,
    Q0=a0^4*i0^2*c^4,
    V0=-a0^2*i0^2*c^4*R0,
    U0=8q0^2*a0,
    Z0=U0 V0,
    e0=-U0^2*v^2*eta0^4.

Then the top form simplifies exactly to

    (P13_CRT)_1088
      =2^112*q0^64*a0^128*i0^64*c^128*
         R0^16*v^16*eta0^32.

It is nonzero. The coefficient of

    J^480*w^160*v^208*h^32*r^64*c^128*z^16

is exactly

    2^976*3^640*beta^480>0.

The h^32 exponent uniquely chooses the h*a0 term in k0 throughout
eta0^32; z^16 then uniquely chooses the q0^4*z term in R0 throughout.
The remaining factors are monomials, giving the stated coefficient.
This verifies the numerical coefficient slice without depending on the
other five fixed ports.
