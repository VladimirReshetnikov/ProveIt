# Three roots in one coordinate: 15 unrestricted integers, degree 214

This construction is an ordinary mathematical reduction of the incoming
`con_zfc_pell_congruences_2026-10-23/transport/degree88_17.json` polynomial.
The native/compiler/K215 calibration remains an inherited theorem. All six
fixed coefficient ports are unchanged. All abbreviations are polynomials.

## Distinct valuation lemma

Let p be a prime. Let A_1,...,A_m be nonzero rationals with pairwise distinct
even p-adic valuations. If a signed sum of their square roots is rational,
then every A_i is a square in Q.

Proof: collect the radicals by their classes in Q*/Q*². Square roots of
distinct squareclasses are linearly independent over Q, by the character
projections of the finite multiquadratic Galois group. Within each class,
the rational multipliers of one chosen representative have distinct p-adic
valuations. Their sum cannot vanish, by reducing the uniquely least-valued
term modulo p after clearing denominators. Therefore no nontrivial class
occurs. This argument also handles negative radicands in an algebraic
closure; no unproved positivity is needed.

## Source and arithmetic guards

Use the parent abbreviations J=3J3+1, q=beta J+1, W=4(3w3+1), X=qW,
Y=(2v+1)q³, E=XY, a=(X+1)Y, H=4a+3, Delta=a²+H,
k=R+1+hE, eta=c-Yk, zeta=k-eta, I=(2r+1)c²,
Q=I², V=fcT-f²R-c. The joint guard implies eta*zeta>0; hence
|c|>(|Y|-1)|k|>1, so Q>1. The odd H is nonzero.

Put u=EYk, P=2u+k, A=u(u+k)+1, delta=Q-1,
D0=X+ac, Cmain=Delta c²+1, and (only in the proof)
B=(QV²-1)/delta.

Because beta=1 mod3, J=1 and W=1 mod3, we have q=X=2 mod3,
a=0 mod3 and Delta=H=0 mod3. The retained strong row
Q=Delta(f²-1) forces 3|I. Thus delta=-1 mod3. Writing b=XY²,
b is 0 or 2 mod3 and A=1+b(b+1)k²=1 mod3. Also B=1 mod3
in the rational ring localized away from3, and Cmain=1 mod3.
Consequently the radicands 36H²A, 324H²B, 4Cmain have respective
3-adic valuations 2v3(H)+2, 2v3(H)+4, 0: distinct even integers.

## The three quadratic eliminants

Delete the parent's half-centered first root tau, auxiliary gap y_gap,
and main congruence quotient gamma. Add xi. Define:

    b1=6P, c1=9(k²-4),
    a2=delta, b2=36delta V, c2=324(1-V²),
    a3=H², b3=4HD0,
    c3=4(X²+2acX-Hc²-1)=4(D0²-Cmain).

Let Q1(r)=r²+b1r+c1, Q2(s)=a2s²+b2s+c2,
Q3(w)=a3w²+b3w+c3. The formal r,s,w are elimination
indeterminates, not quantified unknowns. Define:

    T(z)=a2z²+b2z+c2-a2c1,
    U(z)=2a2z+b2+a2b1,
    F12(z)=T(z)²+b1T(z)U(z)+c1U(z)²,
    N(xi)=Res_w(Q3(w),F12(xi-w)).

This resultant is the determinant of a fixed 6-by-6 Sylvester matrix.
The accompanying JSON supplies its full 568-term expansion with fixed
integer coefficients. Thus N is a literal ordinary polynomial.
Its leading xi coefficient is delta^4 H^8, which cannot vanish here.

Completeness: from a parent solution take
xi=3tau+18y_gap+2gamma. The three summands are roots of Q1,Q2,Q3,
respectively, so N=0.

Soundness: a zero of N supplies roots whose sum is xi. Their quadratic
formulas give a signed radical identity

    H(xi+3P+18V)+2D0
      = ±6H sqrt(A) ±18H sqrt(B) ±2 sqrt(Cmain).

The left side is an integer. The distinct-valuation lemma proves that
all three radicands, and hence A,B,Cmain, are rational squares.
Choose the corresponding signed rational roots t,y,D. Since t² and D²
are integers, their reduced denominators are one. Rational y satisfies
QV²-(Q-1)y²=1 and is an integer by adjacent-coefficient Pell descent.
Thus r=6t-3P and s=18y-18V are integers. Then w=xi-r-s is an integer;
Q3(w)=0 mod4, with H odd, implies w even. Restore

    tau=2t-P, y_gap=y-V, gamma=w/2.

All three discarded rows return exactly. No integer divisibility is
inferred merely from a rational resultant.

For completeness, the adjacent-coefficient descent is as follows. If
QV²-(Q-1)y²=1 with Q>1,V integral and y=a/m reduced, then m² divides Q-1.
For |V|>1 use positive absolute values and set
V'=(2Q-1)V-2(Q-1)y, y'=(2Q-1)y-2QV. The equation is preserved,
V' is an integer with 0<|V'|<|V|, and y' has the same reduced
denominator m because 2Q-1=1 modm. Descend to |V|=1, where |y|=1.

## Single polynomial and exact degree

Retain S=Q-Delta(f²-1) and the parent's joint guard G. The final equation is

    (1+4S)(1+4G)(1+4N)-1=0.

Each factor is an integer congruent to1 mod4. A product equal to1 forces
each factor to be1: the only possible integer units are ±1, and -1 is
excluded modulo4. Thus this is exactly S=G=N=0.

The source gives degS=14 and degG=44. The generic inputs
xi,b1,c1,a2,b2,c2,a3,b3,c3 have respective degree bounds
1,17,14,6,13,14,12,13,9. All 568 terms have weighted degree ≤156.
Their maximal-weight sum factors as

    b1^4 a2^2 a3^3 (xi*b2+c2)
       [a3*(xi*b2+c2)+b3*b2].

Write subscript0 for the highest homogeneous part. Since H0=4a0,
D0,0=a0*c, b3,0/a3,0=c, b2,0=36Q0V0 and c2,0=-324V0²,
the actual leading form is

    1296 (12u0)^4 Q0² H0^8 V0²
      (Q0*xi-9V0)(Q0*(xi+c)-9V0).

This is nonzero for the authentic beta: all displayed factors are nonzero
polynomials, and the last factors have nonzero xi coefficients.
Hence degN=156 exactly. The final top form is64*S0*G0*N0, also nonzero,
so the single polynomial has exact degree214 in15 unrestricted integers.

The zero-existence equivalence is formalizable in ZFC and composes with
the explicitly inherited native and refutation calibration. Negation gives
the requested no-solution/Con(ZFC) equivalence. This is not a new compiled
Lean/Rocq certificate or a claim of global minimality.
