# A quartic in 42 unrestricted integers by recovering a common sign

## Statement and fixed source

Use the complete coefficient tuple of ProveIt package 57's `quartic45.json`,
with the already shifted high-mask port `MF`. The comparison snapshot is
`beb0192cb8dc36f78c369c080f2adfbc1887a486`. No port is changed.
There is an explicit quartic in 42 unrestricted integer variables whose
solvability is equivalent to the solvability of that source quartic, and
hence, by its stated ordinary compiler/calibration theorem, to a finite
ZFC refutation. The new polynomial is the sum of the squares of 27 explicitly
listed quadratic residuals. Its coefficient of `tau^4` is 1.

The reduction saves three unrestricted integer variables at the same exact
degree four. It makes no assertion about globally minimal quartics, the
nine-positive frontier, or a new proof-assistant certificate.

## The explicit modification

Write `Pos(x,y,t)=1+x^2+y^2+t(t+1)`. It is positive for every integer triple
and represents every positive integer, by the three-square theorem applied
to `4n-3`.

Keep source residuals 1 through 22 and 26 through 28 unchanged. Replace
residual 23, `w-u^2`, by `w-4u^2`. Delete residuals 24 and 25, which say
`eta=Pos(eta_pos1,eta_pos2,eta_pos3)` and
`zeta=Pos(zeta_pos1,zeta_pos2,zeta_pos3)`. Delete their six private
variables. Add three new variables `EZ_pos1,EZ_pos2,EZ_pos3` and the residual

    eta*zeta - Pos(EZ_pos1,EZ_pos2,EZ_pos3).

Thus `45-6+3=42` variables and `28-2+1=27` residuals remain. Every residual
has total degree at most two. The changed square scale has no new variable
and no higher degree. The formulas in `quartic42.json` are a complete
polynomial definition, not a compiler pseudocode specification.

## Soundness before any sign recovery

Take an integer common zero of the new residuals. The retained source guards
give

    q=beta*J+1=2*q_half_root^2,
    F*alpha>0, F*(q-F-alpha)>0.

Since `beta>=3`, the first equality forces `J>0`: negative J makes q
negative, and J=0 would make q=1, not twice a square. Thus q>=16 for the
authentic coefficient tuple. Put C=q-F-alpha. The two positive products
make F,alpha,C have the same nonzero sign; their sum q>0 makes all three
positive.

Put s=2*v_scale+1, so s is a nonzero odd integer. The unchanged quadratic
lift equations restore exactly

    X=w*q, Y=s*q^3, E=X*Y, k=eta+zeta,
    c=k*Y+eta, a=(X+1)*Y, H=4*a+3,
    Delta=(a+2)^2-1, D=X+a*c+gamma*H,
    I=(2*r+1)*c^2,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J.

They also restore

    tau^2 - X*Y^2*(X*Y^2+1)*k^2 = 1,
    D^2-Delta*c^2=1,
    I^2=Delta*(f^2-1),
    I^2*V^2-(I^2-1)*y^2=1,
    k=R+1+h*E,
    V=f*o-c=j*c-R.

The new guard says eta*zeta>0, so eta,zeta are nonzero and have a common
sign sigma in {+1,-1}. Set kappa=|k|>0. In particular k has sign sigma and
0<eta/k<1. No sign of Y,c,D,f,I,o,j,h or gamma has been assumed.

The standard source packing estimates use only q,F,alpha,C>0 and the
authentic mask bounds at this stage; they do not use z,eta,zeta or Y:

    q*(q^2-1) < R < q^4-2,  R-2>3q+1.

For reference, `G=q*alpha+(q-1)*C` satisfies `q<=G<=q^2-q`, and
`0<(MC+q*MF)*J<(q-1)*(1+2q)`, which give these bounds. This is the same
preliminary packing bound used in the source proof.

## The factor four creates room for sign recovery

First u cannot be zero. Otherwise w=X=E=0, a=Y and D=a*c+gamma*H.
The main norm, reduced modulo H, is then zero, whereas it equals 1.
Thus H divides 1. But |Y|>=q^3 and H=4Y+3 give |H|>1, a contradiction.
Consequently w=4u^2>=4 and X>=4q>0. With e=|E|,

    |Y|>=q^3>=2, e=X*|Y|>=4q^4>4R+8.

Define A=|a+2| and P0=2X*Y^2+1. Both are positive integers. Directly,

    A>e>R+2, P0>A, Delta=A^2-1>0.

Indeed for negative Y, A=(X+1)|Y|-2>e because |Y|>2; the positive-Y
case is immediate. The inequality P0>A follows from X>=1, |Y|>=2.

Let c0=|c|. For Y>0, c0/kappa lies strictly between Y and Y+1. For
Y<0, it lies strictly between |Y|-1 and |Y|. Therefore c0>kappa>0.
Classification of the two positive Pell equations gives ranks n,p>=1:

    kappa=2*psi_P0(n), |tau|=chi_P0(n),
    c0=psi_A(p), |D|=chi_A(p).

Here chi and psi are the ordinary Pell polynomials. Since P0>A and
c0>kappa, monotonicity gives p>n.

Because P0=1 modulo e, the first Pell recurrence gives kappa=2n modulo e.
The retained index equation thus yields

    sigma*2n = R+1 (mod e).

If sigma=+1, then 2n>=R+1, since 0<R+1<e. If sigma=-1, then
2n>=e-R-1>R+1. Hence in both cases

    n>=(R+1)/2>=24, p>n.

It follows by elementary Pell growth that

    c0>A*Delta^2, c0>2p, c0>2R.

For example p>=6 already gives the first inequality: psi_A(6) exceeds
A(A^2-1)^2 for every A>=2, and psi_A is increasing. The second follows
from psi_A(p)>=2p for A>=2,p>=2, with strictness at p>=3; the third
follows from p>=2 and psi_A(2)=2A>2R.

## Recover the main Pell rank without knowing the sign of c

Apply the inherited ordinary strong-rank lemma with A,c0 and |2r+1|:

    (|2r+1|*c0^2)^2=(A^2-1)*(f^2-1),
    c0=psi_A(p)>A*(A^2-1)^2.

It gives a positive rank m with

    |f|=chi_A(m), p divides m, c0 divides m,
    m>=c0>2p, |I|=(A^2-1)*psi_A(m).

This lemma is coefficient independent. It is proved in the inherited
ordinary-kernel proof, section 'Bootstrap and ordinary strong-rank
recovery'; substituting c0 and |I| meets exactly its stated hypotheses.

The auxiliary norm excludes V=0 and y=0 and has Pell parameter |I|>1.
Its classification gives an odd rank ell=2v+1 with

    |I|*|V|=chi_|I|(ell), |y|=psi_|I|(ell),
    |V|=Q_v(I^2),

where the integer polynomial Q_v satisfies

    Q_v(1-A^2)=(-1)^v*psi_A(ell),
    Q_v(0)=(-1)^v*ell.

The exposed identities V=f*o-c and V=j*c-R supply exactly the needed
congruences, without reconstructing a quotient variable:

    V=-c (mod |f|), V=-R (mod c0).

Modulo |f|, I^2=1-A^2, so the first congruence gives
psi_A(ell)=+c0 or -c0 modulo |f|, irrespective of the signs of c and V.
Squaring and using the Pell doubling formula gives

    chi_A(2ell)=chi_A(2p) (mod chi_A(m)).

The inherited signed step-down lemma, whose hypotheses 0<2p<m have
just been proved, gives ell=+p or -p modulo m, hence modulo c0.
On the other hand c0 divides I, so Q_v(I^2)=(-1)^v*ell modulo c0;
the second exposed congruence gives ell=+R or -R modulo c0. Thus
p=+R or -R modulo c0. Because 0<p,R<c0/2, this forces p=R.
This argument does not require the signs of eta,zeta or c in advance.

## Recover eta,zeta, then reuse the source theorem

If sigma were negative, the index congruence would make e divide
2n+R+1. But n<p=R and e>4R+8 give

    0<2n+R+1<3R+1<e,

a contradiction. Hence sigma=+1, so eta,zeta>0.

At this point every hypothesis needed by the source Q45 soundness theorem
is available. Represent eta and zeta separately by Pos, and replace its
old scale coordinate u_old by 2u. Then w=u_old^2 and every one of its
28 residuals vanishes. The source theorem handles the remaining signed
odd Y, recovers s>0 and the transport guard z>0, and decodes the compiler.
Thus a zero of the new quartic yields a zero of the authenticated Q45.
No use of that whole theorem preceded the recovery of its missing guards.

There is a harmless off-by-one transcription in the source Q45 proof's
transport discussion. Its literal residual, retained here, is
`(K0+w)*C-F-z*(q-1)`, so the equation is `(K0+w)*C=F+z*(q-1)`.
The source prose instead displays `z-1` and asserts z>1. The needed and
correct conclusion for the literal circuit is z>0: after source Pell
recovery, w>q>F and C>=1 imply `(K0+w)*C>F`, hence `z*(q-1)>0`.
This suffices to restore the original positive guard. No residual or
coefficient is changed by this correction.

## Completeness

If the source compiler has an accepting computation, its canonical
witnesses satisfy q=2^t with t odd, R odd, and

    w=2^(R-t), R>3q, q>=16.

Thus R-t is even and at least four. Put

    u=2^((R-t-2)/2),

an integer for which w=4u^2. The canonical eta,zeta are positive;
represent their product by Pos and retain all the other arithmetic
witnesses and guards. This gives an integer zero of the new quartic.
This is an existence-equivalence construction, not an identity on every
old tuple. The ability to choose canonical compiler witnesses is used
explicitly.

## Consequence and verification boundary

Composition with Q45's explicitly bound ordinary compiler and K215 endpoint
gives, by arithmetic formalizable in ZFC,

    ZFC proves: no integer zero of Q42 iff Con(ZFC).

The artifact does not supply a new end-to-end Lean/Rocq certificate or an
object-language ZFC derivation. The code checks exact quadratic residuals,
variable occurrence, degree and the tau^4 coefficient. Such finite checks
verify the polynomial definition and algebra, not the unbounded compiler
semantics or the truth of consistency.

The ordinary strong-rank and signed step-down lemmas, source arithmetic
lift, odd-scale theorem, compiler constants and endpoint are inherited.
The new contribution is replacing two independent positivity guards by
one common-sign guard while strengthening an existing square scale enough
to force the common sign after rank recovery.
