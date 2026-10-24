# Independent arithmetic review of the 93-operation, degree-278 equation

## Conclusion and scope

The new ten-positive construction passes this independent review. Its new
arithmetic reduction is sound relative to the explicitly retained Pell,
native-source, and finite-refutation calibration theorems. The reviewed
equation has ten strictly positive integer unknowns, 93 live binary
operations (55 multiplications, 22 additions, 16 subtractions), and exact
total degree 278. The audit does not assert that it has ten unrestricted
integer unknowns.

The source snapshot is ProveIt commit
`84e16e43092614bae262ca59651cb9d77e31a255`. The actual numerical instance
uses the complete BFS-renamed compact44 tuple; its K0 is distinct from the
original compact44 K0. This audit checks all four actual coefficient hashes
and evaluates their bytes. The supplied BFS transfer is an inherited
mathematical dependency, rather than a consequence of those hash checks.

The reviewer did not import the new builder, its checker, or an inherited
executable. `ten_saturation_review.py` is a separate standard-library
program. It verifies the full tail by exact integer-polynomial arithmetic,
proves the degree cancellation and nonzero leading form, checks topology
and liveness, and compares the whole graph with an independently written
front end and a literal four-conjugate product at 240 modular assignments.
The finite controls are not proofs of the unbounded compiler theorem.

No new Lean/Rocq theorem, encoded object-ZFC derivation, consistency proof,
global minimum, or external historical priority claim is supplied by this
review. Square-root saturation itself already occurs in the pinned
nine-positive work. The present result uses it in a different adjacent-norm
and transport construction.

## 1. The genuinely new algebraic step

Use the manuscript's names D, Delta, I0, Bf, Q, V, M, and Z. In particular,

    D = 1 + V0(V0+1)k^2,
    I0 = i c^2,
    Bf = 1 + Delta D I0^2,
    Q = Delta^2 D I0^2,
    r^2 = D Bf,
    y^2 = (Q V^2-1)/(Q-1).

The polynomial is the denominator-cleared two-root norm

    [(Q-1)Z^2-M^2((Q-1)D Bf+Q V^2-1)]^2
        -4(Q-1)M^4 D Bf (Q V^2-1).

Only after its zero forces D and Bf to be squares is the strong ordinate
defined as I=I0*tau, where tau^2=D. The circuit's register called `I` is
I0; treating it as the true Pell ordinate would be a proof error. The
manuscript distinguishes these roles correctly.

The important choice is one power of D in Bf, rather than D^2. It implies
Bf=1 modulo D and produces the polynomial center

    P = A I0 D,
    P^2-r^2 = D(I0^2D-1)>0.

Thus P is an upper bound for the product root. It has the same highest
degree as r while its squared excess has substantially lower degree. Both
features are used, separately, in transport soundness and the degree proof.

## 2. Root recovery has no hidden sign or equality exception

Every declared input is positive. Consequently q>=32, A>4, c>=3,
I0>=c^2, D>1, Delta>1, Q>1, Bf>c+2, and Bf<Q-1. These inequalities
hold before any polynomial zero or native packing bound is used.

Put b=c(T+alpha)-R. It is an integer but is not yet assumed positive.
If b=0 then V=-c, so |V|>=3. If b is nonzero then

    |V|=|Bf b-c|>=Bf-c>1.

Therefore both radicands r^2 and y^2 are strictly positive for all positive
inputs. M is positive and Q-1 is nonzero. A polynomial zero gives a rational
signed sum Z/M=epsilon*r+eta*y.

The equal-root case cannot occur. Clearing y^2=r^2 gives

    (Q-1)D Bf=Q V^2-1.

Since D divides Q, reduction modulo D would give 0=-1. This contradicts
D>1. Thus the signed sum is nonzero. If x=epsilon*r+eta*y is rational,
then

    2 epsilon x r=x^2+r^2-y^2,

so both roots are rational. The integer radicand makes r integral. The
coprimality identity gcd(D,Bf)=1 and unique factorization make both D and
Bf positive integer squares, giving positive integers tau and f.

For y, the adjacent-coefficient descent is needed: a rational root is not
declared integral merely because the fraction is displayed. If

    QV^2-(Q-1)y^2=1, Q>1, V in Z, y in Q,

write y=a/d in lowest terms. Then d^2 divides Q-1. After absolute values,
for V>1 the norm-preserving transformation

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

has integral V', the same reduced denominator d for y', and |V'|<V.
Indeed y>V and (Q-1)y<QV. The norm excludes V'=0. Descent reaches
V=1,y=1, so d=1. This argument works for every integer Q>1; it does not
prematurely assume that Q is a square.

It is now legitimate to put I=I0*tau. This gives

    c^2 | I, I>=c^2, f^2-Delta I^2=1, Q=(Delta I)^2.

No oddness of I or of I/c^2 is needed anywhere in this positive-domain
argument. This matters because the completeness construction below does not
preserve such an oddness condition.

## 3. Dependency order in soundness

The strong/auxiliary all-index folding theorem can now be used: its
hypotheses are integral f,y,I, the actual strong norm, c<=I, c^2|I, and
V=-c modulo f. It gives c=psi_A(p), with p positive and odd. The first
Pell norm supplies k=2 psi_(2V0+1)(n0). If n0=1, c=2Y+1 lies strictly
between psi_A(1) and psi_A(2), which is impossible. Therefore n0>=2 and

    c>8X mu^2 Y^2.

This estimate precedes transport positivity, p=R, q's parity, and all
denominator cancellation. In particular it is not circularly deduced from
X=2^R.

For completeness of the local bound audit, the retained mask estimate is
R<q^4+(alpha+2)q^2. Since X>=q and mu=q^2+1, the last displayed c
bound implies R<c alpha/4 for every alpha>=1. Hence b>0 and V>1.
If R<0 then |k-R-1|<c-R<b. If R>=0 then |k-R-1|<c+c alpha/4+1,
whereas b>c(1+3alpha/4); the very large mu^2 gives
|e/mu^2|<b/2 in both cases. Finally,

    y-V=(V^2-1)/((Q-1)(y+V))
        <V/(2(Q-1))<Bf b/(2(Q-1))<b/2.

The product center P>r is unconditional. Write t=Bt/(q-1),
s=Y/q^3, rho=e/mu^2, and kappa=Kpos/H temporarily as rational numbers.
The exact center identity gives

    n=epsilon*r-P+(eta*y-V)-kappa-s+W t+rho,
    W=1+(q-1)b.

Kpos>0 follows from the same c estimate. If Bt<=-1 then
W t<=-b-1/(q-1). Every sign choice consequently makes n<0. This
contradicts the declared positive domain. Thus Bt>=0, C>0, and the
native packing bound 3q<R<q^4-2 is licensed.

Only after this step does the inherited rank argument use c>2R to obtain
p=R. Odd p then makes R odd. The fixed parity of the masks makes q even
and J odd. The proof uses gcd(mu^2,q^3(q-1)H)=1 only at this later point:
H is -1 modulo mu, and gcd(q^2+1,q-1)=1 when q is even. Integral r,y,P
therefore recover mu^2|e. The old short-index, whole-product height,
projection, and half-binomial arguments have unchanged hypotheses and
unchanged physical parameters A,X,Y,c,k,R. They recover X=2^R, the
transport divisibilities, and fresh unscaled source witnesses.

In particular, the argument does not cancel a possibly nonunit projection
factor modulo H, does not assume the sign of a norm factor's center, and
does not infer native calibration from modular test outcomes.

## 4. Saturated completeness really is available

Start with canonical native data and rebuild the first Pell witnesses at
the same scaled A, giving c,k,tau and the positive eta,zeta. Let
L=c^2*tau. The integer matrix

    [[A, Delta], [1, A]]

has determinant 1, so modulo L it lies in a finite group. Some positive
power is the identity. For that positive exponent m, its first column is
(chi_A(m),psi_A(m)), and L divides I=psi_A(m). Pell growth makes I
positive. Thus

    i=I/(c^2*tau)>0, I0=i c^2,
    f^2=1+Delta I^2=1+Delta D I0^2.

This is a new choice of the strong witness, not an unsupported claim that
an arbitrary old witness already has the required divisibility. No odd m
or odd strong multiplier is requested. A positive matrix period is enough.

At canonical R=3 modulo 4, put S=Delta I, Q=S^2 and

    V*=chi_S(R)/S, y*=psi_S(R),
    T*=(V*+c+R f^2)/(c f^2).

The odd-index polynomial gives V*=-c modulo f^2, because
S^2=-Delta modulo f^2 and c=psi_A(R). It also gives V*=-R modulo c,
because c divides I. As gcd(c,f^2)=1, T* is integral. These congruences
depend on the strong norm and c^2|I, not on any specially chosen original
strong index. Consequently the matrix-period replacement is compatible
with the auxiliary reconstruction.

There is also enough room for both positive variables T and n. Since R>=5,

    V* >= chi_S(5)/S=16Q^2-20Q+5>Q^2,
    u=y*-V*=psi_S(R-1)/S>=psi_S(4)/S=8Q-4.

The gap identity is exact; it uses chi_S(R)=S psi_S(R)-psi_S(R-1).
Since f^2<Q and Q/c>q>alpha, one has T*>alpha, so T=T*-alpha>0.
The main projection gives an integer 0<kappa<Xc, and s=Y/q^3 is a
positive integer. Moreover P<Q and s+kappa<Xc+Y<c^2<Q. The choice

    n=W t+rho+tau*f+u-P-s-kappa

is therefore integral and positive: its two negative groups total less
than 2Q, while u>=8Q-4>2Q. The remaining terms are nonnegative.
This constructs a zero of the new norm with its intended positive domain.

## 5. Exact degree and arithmetic cost

The independent live-node census gives 93 operations. This is a count of
binary addition, subtraction and multiplication, including scalar
multiplication and squaring. It is neither bit complexity nor a count of
expanded monomials. All ten witnesses and four fixed ports occur live.

Set E=Z-M(V+P), L=P^2-D Bf, and delta=Q-1. The exact prefix has

    deg(M,V,P,L,Q,E) <= (13,42,28,46,48,19),
    L=I0^2 D^2-D.

Define B=M^2 L+2MPE+E^2 and C=delta B-M^2(V^2-1). An exact expansion,
checked independently in the free integer polynomial ring, is

    N=4delta V^2 M^2(delta B-M^2 D Bf)
      +4delta V M(MP+E) C+C^2+4delta D Bf M^4.

The four terms have degrees at most 278,264,240,156. The unique
degree-278 contribution is 4Q0^2 V0^2 M0^4 L0. Substitution of the actual
leading forms yields

    N_top=2^10 q0^146 i^10 w^28 Y^60(eta+zeta)^32(q0-F)^2,
    q0=beta J.

The coefficient at J^146 i^10 w^28 Y^60 eta^32 F^2 is
2^10 beta^146>0. Its exponents total 278, so the upper bound is attained
for the actual numerical tuple, independently of the relation among the
other three fixed ports. This is stronger than syntactic degree
propagation or testing at generic values.

## 6. Verification receipts and remaining boundary

The separate checker passed in normal and optimized modes. Its receipts record the exact
equation hash and all four raw coefficient hashes. It verifies eight exact
algebraic identities, the entire twelve-gate norm tail, the center degree
identity and leading coefficient, 6,000 front-register modular comparisons,
240 formal four-conjugate output comparisons, and small arithmetic and
matrix-period controls. Its acceptance conditions do not use Python `assert`
statements.

These checks do not establish the inherited native-language equivalence or
the consistency calibration. Those remain named ordinary mathematical
dependencies in the main manuscript. The supported conclusion is a new
ordinary arithmetic equivalence and a fully specified smaller positive
polynomial, not a newly completed internal-ZFC proof.

A possible signed-domain transfer requires extra work. The old signed
kernel imposes an odd strong multiplier. Although a recovered first root
is odd there, a generic finite-period saturation may force an even strong
ordinate. The positive-domain proof above has no such restriction. No
thirteen-integer improvement is claimed from that unproved transfer.
