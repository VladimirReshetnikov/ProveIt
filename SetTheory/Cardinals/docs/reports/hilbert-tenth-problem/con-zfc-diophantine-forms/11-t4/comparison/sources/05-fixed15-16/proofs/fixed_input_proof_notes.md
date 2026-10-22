# Fixed-input deletion and fifteen-variable root elimination

This is a proof audit of the new reductions, relative to the complete valid
fixed-program coefficient recipe of the pinned ProveIt H10 construction.
The coefficient recipe, including its shifted MF convention, is an essential
hypothesis. Arbitrary numerical constants satisfying a few bounds do not
substitute for that recipe.

Source commit: `cdd582bec13f908df3711fa9e05d1ddac368a5db`.
All file names in the source-span table below are relative to
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`.

## 1. Notation and exact six-factor system

Use positive fixed numerals B=2^d>=16, odd b>=1, b<=d, and the native
compiler's K, MC, MF. MF is the *shifted* mask in the actual84 source.
Set the fixed ordinary input to x=1 and define the fixed numeral

    u=2d+b,  W0=2^u.

Thus u is odd and u>=3. No exponent depending on an unknown remains.
The sixteen strictly positive variables are

    J,F,alpha,t,f,h,i,T,s,w,tau,eta,zeta,y,Z,gamma.

Here t is the transport quotient and T is the auxiliary quotient. Define

    q=(B-1)J+1, X=wq, Y=sq^3, E0=XY,
    k=eta+zeta, c=kY+eta,
    a=Y(X+1), A=a+2, Delta=A^2-1, H=4a+3,
    Dmain=X+ac+gamma H,
    C=Z+W0,
    L=q-F-2Z-W0-alpha-2d,
    R=(q(q-F)-Z)(q^2-1)+(MC+q MF)J,
    S=Delta i c^2, Q=S^2,
    V=c(Tf-1)-Rf^2.

The six normalized factors are

    Nfirst=tau^2-XY^2(XY^2+1)k^2,
    Nmain=Dmain^2-Delta c^2,
    Naux=Q V^2-(Q-1)y^2,
    Nindex=k-hE0-R,
    Ntransport=(K+w)C+q-F-t(q-1),
    Nstrong=f^2-Delta i^2 c^4.

Put P6=Nfirst Nmain Naux Nindex Ntransport Nstrong. The fixed-input
system is L=0 and P6=1. Equivalently it is the single polynomial

    P6(1+L^2)-1=0.

The scaled-strong implementation instead uses Delta*Nstrong as its
strong factor and subtracts Delta at the end. Since Delta>0 on the
positive domain, it has exactly the same zeros. This distinction must
be respected when counting or evaluating the emitted SLP.

At a zero L=0, the old parent source's computed word is exactly

    q-F-Z-alpha-2d=Z+W0=C.

Thus all retained parent fields agree literally. In particular,

    C>0, F+Z<q, 0<W0<q.

These bounds precede every Pell, dyadic-radix, typing, or acceptance
claim; there is no omitted C>=0 assumption.

## 2. Signed pre-input kernel extracted from the existing proofs

We need the following precise version of the inherited argument.

**Lemma (no input bridge required).** Keep the complete valid compiler
constants. Suppose all sixteen displayed variables are positive except
that T may be any integer, and suppose f>0, L=0 and P6=1. Then all six
factors are 1, R is odd, and

    R>3q+1, R+2<q^4<=XY<a,
    c=psi_A(R), Dmain=chi_A(R), X=2^R<a,
    q is a power of two.

Here chi_A(n)+psi_A(n)sqrt(A^2-1)=(A+sqrt(A^2-1))^n.
The lemma does not assert T>0. It does not assume the deleted input
norm, the gamma split, a valid tableau, or an accepted input.

### Proof and exact dependence audit

Every factor is an integer unit. The main and normalized strong factors
cannot be -1 modulo4: Delta=A^2-1 is 0 or3 modulo4. Since Q is a square,
Naux is congruent to a square modulo4, so it also cannot be -1. The
negative first norm is impossible by the standard strict Pell descent:
for U=XY^2>1, a positive solution tau^2-U(U+1)k^2=-1 would have
Uk<tau<(U+1/2)k. The transformation

    k'=(2U+1)k-2tau,
    tau'=(2U+1)tau-2U(U+1)k

has 0<k'<k and preserves the norm -1, contradicting a least positive k.
Consequently the four norm factors are 1; the index and transport
factors have one common sign epsilon in {-1,1}. This is exactly the
unit argument of normalized85 with its irrelevant input-norm factor
deleted. No remaining factor or equality uses delta or rho.

The already proved F+Z<q and native mask bounds give

    2q-1<=q(q-F)-Z<=q^2-q-1,
    0<(MC+q MF)J<(q-1)(1+2q),

hence

    (2q-1)(q^2-1)<R<q^4-q^3,
    R>3q+1, R+2<q^4<=XY<a.

These are bounds over ordinary integers before proving q is dyadic.
They are the same bounds as normalized85 Section2; the new loader
equality directly supplies the positivity that its transport argument
previously recovered.

Put P=2XY^2+1. The first and positive main norms yield indices n,p>=1:

    tau=chi_P(n), k=2psi_P(n),
    Dmain=chi_A(p), c=psi_A(p).

The index unit gives 2n=R+epsilon+vXY with v>=0. Since P>A and c>k,
one has p>n>=(R-1)/2>=24. Also c>2R and c>2p. The strong equation
gives f=chi_A(m) and psi_A(m)=i c^2. Strong divisibility and the Pell
addition formula give pc|m, hence c|m and m>2p.

The auxiliary congruences, valid for signed T, are

    V=-c modulo f, V=-R modulo c.

The second uses f^2=1 modulo c. Classify the absolute auxiliary root:
|SV|=chi_S(ell), y=psi_S(ell), with ell odd. If ell=2v+1, then
V=e Q_v(S^2), e in {-1,1}, where Q_v(0)=(-1)^v ell and
Q_v(-Delta)=(-1)^v psi_A(ell). Squaring the first congruence gives
chi_A(2ell)=chi_A(2p) modulo f. The strict Pell step-down at
f=chi_A(m), with m>2p, gives ell=+/-p modulo m and therefore modulo c.
The second auxiliary congruence then gives R=+/-p modulo c. Since
0<R,p<c/2, p=R. This is the signed proof; it never assumes V>0 or T>0.

Now v>=1 in 2n=R+epsilon+vXY contradicts n<R and XY>R+2. Thus
2n=R+epsilon. The sign epsilon=-1 is excluded by Pell duplication:
2A^2-1>P and A>Y+1 give

    psi_A(2n)=2A psi_(2A^2-1)(n)>=A k,

whereas c=psi_A(2n+1)>Ak>k(Y+1) contradicts
kY<c<k(Y+1). Hence epsilon=1, both remaining factors equal1, and R is odd.

For power recovery set r=(R-1)/2>=24 and
xi=(X+1)^(2r)/X^r. The elementary Pell recurrence estimates in the
signed-source power proof give

    c/(k/2)>xi,   Y>xi/2-1>X^r/3,
    a>X^(r+1)/3>2^R.

The strict comparison uses only 6XY^2>a, X>=16, Y>=q^3 and the displayed
ratio interval; it does not use an input Pell tuple or auxiliary sign.
For e_n=chi_A(n)-a psi_A(n), the recurrence gives e_n=2^n modulo H.
The main definition is e_R=X+gamma H. Since 0<X,2^R<a<H, this congruence
is exact: X=2^R. As q|X, q is a power of two. This finishes the lemma.

The rank argument is the body of signed-quotient absorption Section2
(lines35-92), with its unused input-norm +1 factor removed and gamma
supplied independently. The power argument is signed-quotient
soundness Section2 (lines41-69). The only uses there of the original
gamma=rho+sigma syntax are that Dmain>0 and its displayed main-root
identity holds; both are supplied here. That explicit extraction is
necessary: neither theorem about a *full* parent zero may be applied
before restoring its missing input tuple.

## 3. Explicit restoration of the deleted input tuple

Apply the lemma to a fixed16 zero (or to one with signed T as above).
The fixed loader already gives W0=2^u<q<=X=2^R, so u<R. Also u is odd
and at least3. Define

    kappa=psi_A(u), mu=chi_A(u),
    delta=(kappa-u)/Delta,
    rho=(mu-a kappa-W0)/H,
    sigma=gamma-rho.

Every quotient is now proved integral and positive, not postulated.

### Delta quotient

The binomial expansion of (A+sqrt(Delta))^u gives
psi_A(u)=u A^(u-1) modulo Delta. Since A^2=1 modulo Delta and u is odd,
kappa=u modulo Delta. Moreover A>=3 and u>=3 imply psi_A(u)>u by the
positive Pell recurrence. Thus delta is a strictly positive integer.

### H quotient

Write e_n=chi_A(n)-a psi_A(n). It satisfies

    e_0=1, e_1=2, e_(n+1)=2A e_n-e_(n-1).

Since H=4A-5, the sequence 2^n satisfies the same recurrence modulo H:
2^(n+1)-2A*2^n+2^(n-1)=-H*2^(n-1). Induction therefore gives
e_n=2^n modulo H for all n>=0. Hence rho is integral.

The sequence e_n is positive and strictly increasing. For n>=1,

    e_(n+1)>(2A-1)e_n>2e_n.

Therefore e_u>2^u for every u>=2; rho is strictly positive.

### Positive gamma gap: an explicit uniform inequality

Because R>u>=1,

    e_R-e_u >= e_(u+1)-e_u
             > (2A-2)e_u
             >= 4A-4
             > A
             > X=2^R.

The main root gives gamma H=e_R-X. Consequently

    H sigma=e_R-e_u-X+2^u>0.

Thus sigma is a strictly positive integer. This proof does not rely
on a claim that padding makes an arbitrary Pell completion positive;
it constructs the intended small-index completion and proves its gap.

The four identities

    kappa=u+delta Delta,
    mu=W0+a kappa+rho H,
    mu^2-Delta kappa^2=1,
    gamma=rho+sigma

restore literally the missing parent85 input norm and gamma producer.
Together with the retained factors and the exact word C, they give a
full parent85 zero at x=1, or equivalently a full parent84 zero. If T
was positive, every parent witness is positive and the existing
compiler theorem applies immediately. If T was signed, this produces
an exact parent84 zero with only T allowed signed, a domain used below.

Conversely, every positive parent84/85 zero at x=1 has the intended
input power W=2^(2d+b) by its established input theorem. Set
gamma=rho+sigma and delete delta,rho,sigma. The old word becomes
C=Z+W0, L=0 and P6=1. Thus the fixed16 system has a positive solution
if and only if the full parent polynomial at x=1 does.

## 4. Fifteen positive variables by eliminating f

Delete f from the fixed16 variable list. All other variables remain
strictly positive. Define the following integer polynomial expressions:

    Daux=1+Delta i^2 c^4,
    Baux=c+R Daux, Uaux=cT,
    Arat=Q(Daux Uaux^2+Baux^2)-(Q-1)y^2-1,
    Brat=2Q Uaux Baux,
    Knorm=Arat^2-Daux Brat^2,
    P4=Nfirst Nmain Nindex Ntransport.

One fifteen-variable equation is

    P4(Knorm+1)(1+L^2)-1=0.                         (15)

The SLP may compute the same cross term as
4*(Q*Daux*Uaux^2)*(Q*Baux^2) to avoid separately constructing Brat.
Brat is a proof abbreviation when implementing that schedule; it adds
no existential variable and no division to polynomial(15).

### Integer reconstruction

At a positive zero of(15), the integer factor 1+L^2 must be1, so L=0.
The remaining factors P4 and Knorm+1 are units. Brat is even, hence

    Knorm+1=Arat^2+1 modulo4.

This residue is 1 or2 modulo4 and cannot be -1. Therefore Knorm=0 and
P4=1. At L=0 the loader bounds give R>0 as in Section2. Hence Baux>0,
Uaux>0, Q>0 and Brat>0. In particular Brat is nonzero.

Define the rational number f=Arat/Brat. Knorm=0 gives f^2=Daux, a
strictly positive integer. A rational number whose square is integral
is integral: in a coprime fraction p/q, q^2|p^2 forces q=1. Thus f is
a nonzero integer.

The literal auxiliary expression at this signed f is

    V=Uaux f-Baux.

Using f^2=Daux and Arat=Brat*f gives

    Q V^2-(Q-1)y^2
      =Arat+1-Brat*f=1,
    f^2-Delta i^2 c^4=1.

Along with P4=1 these restore exactly L=0,P6=1, provisionally with f
signed. No divisibility witness and no unproved choice of root has
been introduced. The signed root is unique because Brat is nonzero.

### Positivity without circular use of the positive compiler

Put fplus=|f| and Tplus=sign(f)*T. Since the source uses f only through
f^2 and Tf, this simultaneous change preserves every six-factor
expression and keeps fplus positive. The signed pre-input lemma of
Section2 applies to fplus,Tplus. It gives X=2^R and the exact main
Pell pair. Section3 then constructs positive delta,rho,sigma and
restores a **full parent84 zero with only its auxiliary quotient
Tplus allowed signed**.

Now, and only now, apply the accepted signed-quotient positivity
theorem: on the full valid native compiler slice, a full parent84
zero with all other supplied witnesses positive has Tplus>0. This is
proved in signed-quotient soundness Sections1-5 and independently
reviewed. Since the original T>0, Tplus=sign(f)T>0 implies f>0.
Consequently the uniquely restored root belongs to the positive
fixed16 domain, and its full positive parent compiler theorem applies.

This order is essential. Applying the full signed-T theorem directly
to the reduced system would omit its input hypotheses; applying the
positive compiler to a signed root would also be invalid. The signed
pre-input extraction and explicit completion remove both gaps.

### Converse

At every fixed16 positive zero, the four norm signs are +1, and the
index/transport signs are +1 by Section2. In particular Naux=Nstrong=1
and P4=1. Then f^2=Daux. Expanding Naux=1 gives Arat=Brat*f, so Knorm=0.
Deleting f therefore gives a positive zero of(15). This proves exact
existence equivalence between the fifteen- and sixteen-variable
constructions; the restored f is uniquely determined.

## 5. Proof dependencies and exact source spans read

| Source | Lines / section | Use |
|---|---|---|
| `review_complete85_auxiliary_bezout_math.md` | 7-30 | Literal normalized85 fields and factors |
| Same | 52-77 | Integer-unit signs and pretyping packing inequalities |
| Same | 107-183 | Strong divisibility, rank identification, index sign |
| `review_complete74_asymmetric_scale_math.md` | 45-100 | Explicit kernel interface excludes input data; asymmetric X=2^R proof |
| `complete84_signed_quotient_absorption.md` | 35-92 | Signed-T rank recovery before any input theorem |
| `complete84_signed_quotient_soundness_scout.md` | 7-40 | Source bindings and inherited signed premises |
| Same | 41-69 | Odd-R power recovery, no positive-T or input assumption |
| Same | 70-186 | Exact half-binomial, mask parity, and full signed-T positivity |
| Same | 187-206 | Separate input dependency audit and signed-f symmetry |
| `review_complete84_signed_quotient_soundness.md` | 1-31 (all) | Independent review and precise theorem scope |
| `complete92_norm_unit_guard.md` | 7-36,68-153 | Integer local norm elimination, even cross coefficient, signed root restoration |
| `complete84_scaled_strong_output.json` | all 84 source rows | Literal retained fields, scaled vs normalized factor, sole f/T consumers |

The notes make no claim of a fresh formal assistant verification of
these new reductions. They are ordinary mathematical proofs with the
inherited theorem interfaces explicitly audited. The new emitted SLP,
operation count, degree calculation and concrete coefficient-generator
binding are separate artifacts owned by the construction audit.

