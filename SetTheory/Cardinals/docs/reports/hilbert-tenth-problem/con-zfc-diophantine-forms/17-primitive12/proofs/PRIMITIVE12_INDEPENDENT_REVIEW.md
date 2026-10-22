# Independent semantic audit of the twelve-positive-variable construction

Reviewed against agent_root_reductions/build_primitive12.py and the
underlying normalized blank-input Pell interface. This is an ordinary
mathematical audit, not a formal proof-assistant certificate. The reviewer
derived the separating estimates and the rational auxiliary-root lemma
independently of the construction author.

## 1. Rational auxiliary roots are integral

**Lemma.** If A>1 and V are integers, y is rational, and

    A^2 V^2-(A^2-1)y^2=1,

then y is an integer.

Write A^2-1=d s^2 with d>1 squarefree and s>0. Put t=sy. Then
d t^2=(AV)^2-1 is integral. In a reduced fraction t=m/n, n^2 divides d;
squarefreeness gives n=1. Thus t is integral. Neither V nor t is zero.

Let F+y0 sqrt(d)>1 be the least positive integer-coefficient norm-one
unit. Classification of positive Pell solutions gives

    A=chi_F(e), s=y0 psi_F(e),
    |AV|=chi_F(n), |t|=y0 psi_F(n)

for positive e,n. Because A divides AV, chi_F(e) divides chi_F(n).
Reducing n modulo 2e and reflecting to 0<=r<=e gives
chi_F(n)=+/-chi_F(r) modulo chi_F(e). Strict growth makes r=e, since
0<chi_F(r)<chi_F(e) for r<e. Hence n=e(2j+1).
Pell composition now gives |t|=s psi_A(2j+1), so
y=+/-psi_A(2j+1) is integral. No large-main-rank assumption is needed.

## 2. Algebraic root set

Use the builder's integer registers and write b=X+ac,
G=1+Delta c^2, I=ic^2, D=1+Delta I^2,
Q=(Delta I)^2, d=Q-1, v=cT, Z=c+RD,
e=Q(Dv^2+Z^2)-1, B=2QvZ.

The four eliminated coordinates satisfy

    gamma=(-b+/-sqrt(G))/H,
    tau=+/-sqrt(A), f=+/-sqrt(D),
    y^2=(e-Bf)/d,

where A=1+ell(ell+k). The norm polynomial encodes

    t=gamma+tau+wy*y+wf*f.

The outer condition Nt=+/-1 yields Cword>=0 and R>0 by the inherited
transport bootstrap. All subsequent separating estimates therefore use
positive Z, C, C2 and the positive Pell/coding parameters.

## 3. The explicit weights separate all sixteen root tuples

Let

    g=c+X, u=ell+k, S=u+g,
    C=v^2+D+Z, r=(a+2)I,
    C2=v+c+Rr,
    wy=Q C S+1, wf=2wy C2+S+1.

Every gamma root has modulus less than g, because

    sqrt(G)<(a+2)c,
    |gamma|<(X+(2a+2)c)/(4a+3)<X+c.

Also sqrt(A)<u and sqrt(A)>ell>g. The last inequality follows directly
from ell=XkY^2 and c=kY+eta with eta<k and Y>=2. Thus the four sums
gamma+tau are distinct and each has modulus less than S.

The integer e^2-B^2D is nonzero. If it vanished, one factor would imply
Q(v sqrt(D)-Z)^2=1. Since sqrt(Q)=Delta I>1 is an integer,
v sqrt(D)-Z would be rational, forcing sqrt(D) to be an integer. But
then Delta I(v sqrt(D)-Z)=+/-1 would be impossible for integers.

Each factor |e+/-B sqrt(D)| is less than Q C^2. Their nonzero integral
product has modulus at least 1. Consequently every y root is nonzero
and satisfies

    |y|>1/(Q C),              wy |y|>S.

For fixed f, switching the y sign therefore changes wy*y by more than
2S in modulus, so it cannot be cancelled by a change in gamma+tau.
This argument remains valid if those y roots are purely imaginary.

For the f-sign separation, sqrt(D)<r and

    |y|<2(v sqrt(D)+Z)<2 sqrt(D) C2.

The first inequality follows from
|y|^2=|Q(vf-Z)^2-1|/(Q-1) and Q>1; the second uses
Z=c+RD and r>sqrt(D). Switching f signs therefore changes wf*f by
2wf sqrt(D), whereas the total possible compensating change in the
remaining terms is less than

    2S+4wy sqrt(D) C2 < 2wf sqrt(D).

All sixteen tuples have distinct values of the indicated linear form.

## 4. Rationality and integrality of a recovered tuple

The polynomial is the product, up to its nonzero integral leading
factor, of the sixteen linear factors associated with these tuples.
A rational zero t therefore chooses one tuple. Every automorphism of
the splitting field fixes t and permutes the sixteen tuples. The
separation result forces the chosen tuple to be fixed componentwise;
all its coordinates are rational.

The monic equations tau^2=A and f^2=D make tau and f integral. Put
V=vf-Z, an integer. The y equation becomes

    Q V^2-(Q-1)y^2=1.

Apply section 1 with A_aux=Delta I. It makes y integral. Finally
gamma=t-tau-wy*y-wf*f is integral too. The recovered coordinates
satisfy the main, first, normalized strong, and auxiliary Pell norms.

The recovered gamma and f can initially have either sign. Soundness
uses the explicitly stated nine-positive-guard theorem in package
12-gap-norm14/proofs/ORDINARY_BLANK_PROOF.md, sections 2--7. Convert the
normalized strong multiplier to i_ordinary=Delta*i>0. Then

    (i_ordinary*c^2)^2=Q=Delta*(f^2-1).

The recovered first, main and auxiliary norms, and the ordinary strong
factor, are all 1; the remaining Nk,Nt are correlated units. Thus this
tuple is a zero of that proof's ordinary six-factor product. Its nine
required positive coordinates are J,F,alpha,z,i_ordinary,s,w,eta,zeta,
all available here. Its remaining coordinates h,f,T,tau,y,gamma are
expressly allowed to be signed. No odd-i or square-w completeness
restriction from the different package 14 theorem is being assumed.
One must not replace gamma by |gamma| directly. The ordinary signed
theorem identifies the true main index and decodes the blank computation.
This is the necessary trust boundary between the new elimination proof
and the inherited compiler theorem.

## 5. Audit of the emitted norm formula

In the integral quadratic algebra f^2=D, let

    z=Ht+b-Hwf*f-Htau,
    K=d(z^2+G)-H^2 wy^2(e-Bf),
    F=K^2-4d^2 G z^2.

The equality F=0 is the elimination of gamma and y from
z=+/-sqrt(G)+Hwy*y and d y^2=e-Bf. The builder computes F=E0+E1*tau
in the algebra tau^2=A, then computes E0^2-A E1^2, then takes the
f norm N0^2-D N1^2. This is exactly the required sixteen-factor norm.
The acyclic pair operations in build_primitive12.py implement these
identities without divisions or new variables.

Modulo 4, F is K^2 in the integral rank-four algebra generated by
f,tau. Both quadratic norms are multiplicative. Consequently the final
P is a square modulo 4. If Nk Nt(1+P)=1, all factors are integer units,
and 1+P cannot be -1 modulo 4. Thus P=0 and Nk,Nt are correlated units.
The recovered signed-core tuple then supplies the inherited argument
that Nk=Nt=1 and the machine halts.

Conversely, take a positive normalized-core witness and set
t=gamma+tau+wy*y+wf*f>0. It is a root of the norm; all outer equations
hold. Therefore the construction preserves existence in both
directions, subject to the explicitly cited compiler/endpoint theorems.

The review found no semantic gap in these steps. Exact operation counts
and multivariate degree certificates are separate finite/algebraic
checks; this note does not certify them merely from their advertised
numbers.
