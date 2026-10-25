# A shared Pell cap for exact powers and modular binomial numerators

## Result and domain

Let `Q_0,...,Q_187` be the complete ordered quadratic residuals in
`equation240/natural/equation.json`, in the literal variable order in that
file. Define the fixed polynomial `P_240 = sum_j Q_j^2`. The variables range
over `N={0,1,2,...}`. Its exact degree is four; its fully collected polynomial
has 25,987 nonzero monomials and maximum absolute coefficient 90,589,484.
The full coefficient definition is `expanded_polynomial.json` beside it.

The ordinary arithmetic proof below, composed with the explicitly inherited
C222/refutation calibration, proves in ZFC

    (there is no natural zero of P_240) <-> Con(ZFC).

It asserts neither consistency nor inconsistency. There is no new Lean,
Rocq, or object-language ZFC proof object. No global optimum or historical
priority claim is made. The different 239-variable contraction has 187
rows, 360,097 monomials and height 491,869,488; it preserves the same source
but trades much denser support for one fewer unknown. Its complete
polynomial and restoration certificate are also supplied.

The previous direct natural endpoint inspected in the incoming archives
has 261 variables, 194 rows, 31,679 monomials and height 85,566,955.
The balanced 240 form saves 21 variables, six rows and 5,692 terms, with
a 5.9 percent increase in coefficient height. These are comparisons within
the direct C222 small-coefficient quartic architecture. Separate ProveIt
polynomials have far fewer variables with different degrees and coefficients.

## 1. What is new, and what is inherited

The incoming `Shared_Binomial_Certificates` construction already identifies
one binomial with both a factorial certificate and the reciprocal CRT
product. It also uses one congruence for the Pell parameter to replace
eleven complete numerator powers by modular residues. That reduces the
exact power requests to six, but retains fifteen complete indexed Pell
certificates. Its complete natural equation uses 319 variables.

Independently, the incoming `Shared_Pell_Bound_261` construction replaces
the full indexed certificate for each requested Pell pair by one indexed
cap and a pooled squared-error congruence. That construction uses nineteen
exact powers and assumes that every capped index belongs to their semantic
size frame.

The new construction combines these representations. The necessary new
interface is that *every modular numerator index must be inserted into
the frame*, even though its enormous power output is absent. The new frame
is still chosen entirely from the semantic arithmetic data before any
private Pell witnesses. Enlarging it remains compatible with the cofinal
choice of the Pell parameter required by the common modular root. The
proof below establishes this simultaneous existence, so the combination
does not assume independent witnesses can be reused unchanged.

The raw source prefix through `modular.common_root` is exactly the parent
prefix: 468 quadratic rows on its first 491 coordinates. The checker
compares every one of these rows and variable descriptions with the frozen
parent. All subsequently changed non-gate rows are checked as exact
polynomial identities. The imported sources and their notices are retained
under `vendor` and `inherited`.

## 2. The semantic arithmetic before the Pell frame

The padded proof horizon is `t=t0+16`. The semantic source has proposed
factorial F, beta-coding parameters x,y, and nine independent positive CRT
representatives. Its arithmetic constants are

    rho=F^2,
    B=b0+2,
    R=2+t+x+y+F,
    K=2R,
    V0=(F^2+1)^t,
    N=B^K,
    q=N^K.

The six retained exact power requests are these first three, together with

    D_t=q^t,   D_y=q^(y+1),   D_x=q^(x+1).

The adjacent denominator is the ordinary product `D_(t+1)=q D_t`.
The sole exact binomial digit will assert `B=binom(F^2+t,t)`. The ten
range requests are the nine independent CRT ranges plus the polynomial
derived-label range. Their upper indices are the nine shifted positive
representatives, the positive derived-label polynomial J, and, for the
one exact binomial, `F^2+t`. All are positive before any power or factorial
is interpreted. The literal positive-gate checker certifies those facts.

The raw ceiling rows are

    V0+B=BF+r+1,       B=r+s+1,

with natural r,s. The meaning of B is deferred until after exact-power and
modular-digit recovery. The complete source, its label formulas, beta
equations and nonnegative Horn polynomial are the unchanged parent source;
their full ordinary proof is retained in `inherited/MODULAR_PROOF.md`.

Let Acal be the set of distinct semantic atoms occurring as base, exponent,
or output of the six exact power requests, together with the upper indices
of all eleven modular requests. Define

    W = 2 + sum_(a in Acal) a.

In the literal source Acal has 23 distinct atoms. In particular the fifteen
independent requested indices k_i are distinct atoms in Acal and are
positive. Consequently `1<=k_i<W` and `m=15<=W-2`. The frame does not
contain its own private Pell witnesses, cap coordinates or residue
quotients. Hence there is no dependence on a witness chosen later.

## 3. A cofinal Pell parameter with a large modulus

Introduce natural L,A,Z,sigma with Z>=1, A=L+sigma, and

    L^2-((W+1)^2-1)(W Z)^2=1.                         (3.1)

For a>=2 define the Pell polynomials recursively by

    X_0(a)=1, Y_0(a)=0,
    X_(j+1)(a)=a X_j(a)+(a^2-1)Y_j(a),
    Y_(j+1)(a)=X_j(a)+aY_j(a).

Every nonnegative solution of the Pell norm with base a is its canonical
pair `(X_e(a),Y_e(a))` for e>=0. The ordinate in (3.1) is positive, so
`L=X_e(W+1), WZ=Y_e(W+1)` for e>=1. The recurrence modulo W gives
`Y_e(W+1)=e mod W`, so W divides e and e>=W. Thus

    A >= L >= X_W(W+1) >= (W+1)^W.

Since W>=3, `(W+1)^W-1>W^3`; in particular `A-1>W^3` and A>W+1.
For completeness choose e=W in (3.1). The congruence gives an integer
Z>=1 and fixes L. Crucially, A remains free to be any larger integer.

Put b=q+1 and

    M = q D_(t+1) D_x D_y.

The common root row is

    2Ab = b^2+1+Mh0,       h0>=0.                     (3.2)

Once the semantic powers have their intended values, M is a positive
power of q. Hence gcd(b,M)=1 and gcd(2b,M) is 1 or 2. In the latter case
b is odd and b^2+1 is even. The linear congruence (3.2) therefore has a
solution class containing arbitrarily large positive A. Choose A in that
class with A>=L and 2Ab>=b^2+1, then define sigma,h0. This proves that
the enlarged frame and the modular-root condition are simultaneously
constructible, rather than merely individually satisfiable.

## 4. One indexed cap

Retain exactly one complete inherited indexed-Pell certificate at index W.
Using names local to this proof, its rows are

    Xc^2-(A^2-1)Yc^2=1,
    U^2-(A^2-1)V^2=1,
    S^2-(Bcap^2-1)T^2=1,
    Bcap=1+4Yc(d+1),
    V=Yc^2(e+1),
    Bcap=A+Uf,
    S=Xc+Ug,
    T=W+4Yc h.

All displayed cap witnesses are nonnegative. The indexed-Pell criterion,
with its usual condition W<=Yc, proves

    (Xc,Yc)=(X_W(A),Y_W(A)).

Here W<=Yc is supplied by the following aggregate row, so it needs no
separate margin variable. The criterion itself is inherited, including
its constructive completeness; it is not replaced by an unproved
fixed-index lemma.

For every requested independent index k_i retain only the principal norm

    x_i^2-(A^2-1)y_i^2=1.                             (4.1)

Add two global rows with natural s_cap,Q:

    Yc=W+1+s_cap+sum_i y_i,                           (4.2)
    sum_i(y_i-k_i)^2=(A-1)Q.                          (4.3)

### Soundness of the cap

Pell classification of (4.1) gives `x_i=X_(j_i)(A)` and
`y_i=Y_(j_i)(A)` for a unique j_i>=0. Equation (4.2) implies y_i<Yc;
strict monotonicity of Y gives j_i<W. The recurrence modulo A-1 gives
`Y_j(A)=j mod (A-1)`. Therefore (4.3) implies

    A-1 divides E=sum_i(j_i-k_i)^2.

Each j_i,k_i lies in [0,W-1], so

    0<=E<=m(W-1)^2< W^3 < A-1.

Thus E=0 and every j_i=k_i. This proves all fifteen indices at once,
including the modular numerator indices newly included in Acal. The
large ordinates themselves are not treated as small residues.

### Constructive completeness of the cap

Set the principal pairs to `(X_(k_i)(A),Y_(k_i)(A))`. Their ordinate
differences y_i-k_i are nonnegative multiples of A-1. Thus the quotient Q
in (4.3) is a natural integer. Since k_i<W,

    sum_i y_i <= m Y_(W-1)(A).

The recurrence gives `Y_W(A)>(2A-1)Y_(W-1)(A)`. Since m<=W-2 and
A>W+1, the difference `Y_W(A)-sum_i y_i` exceeds W. Therefore
`s_cap=Y_W(A)-W-1-sum_i y_i` is nonnegative. The inherited indexed-Pell
completeness theorem supplies the one cap's remaining witnesses. No
private witness from either predecessor is held fixed during this step.

## 5. Recovery of all six powers

For each exact request `(n,k,m)` the retained rows define

    T_n=2An-n^2-1,
    X_k(A)+nY_k(A)=AY_k(A)+m+T_n u.

The natural modulus T_n excludes n=0. All n,k,m are less than W, while
A>W^W. Thus the standard power representation estimates give
`0<=m,n^k<T_n`. The Pell recurrence modulo T_n gives

    X_k(A)+(n-A)Y_k(A)=n^k mod T_n.

The actual pair is already certified by Section 4, so equality of those
two representatives follows: m=n^k. In the forward direction its quotient
u is nonnegative because the Pell expression is positive and congruent to
the least nonnegative residue m. This is the inherited positive-power
lemma at the enlarged frame W; its proof requires only the inequalities
just established, not equality with the former smaller frame.

## 6. Recovery of all eleven binomial residues

From (3.2), substitution `sqrt(A^2-1) -> b-A` respects the quadratic
relation modulo M. The polynomial identity for Pell sequences gives

    R_n=X_n(A)+(b-A)Y_n(A)=b^n mod M.

For n>=1, `X_n(A)>(A-1)Y_n(A)`, so `R_n>qY_n(A)>0`; the n=0 value
would be 1. Every requested numerator pair is now exactly indexed by
Section 4. For each denominator d, qd divides M; also N divides q,
so Nd divides M. The literal modular digit rows are

    R_n=r+dB+qd u,       d=r+s+1,  q=B+o+1

for the exact binomial, and

    R_n=r+Nd u,          d=r+s+1

for a range divisibility. They therefore give the same low-digit
conditions as the original `(q+1)^n` numerators. Their natural quotients
exist for the correct digits because R_n is positive and the selected
residue is its least nonnegative residue modulo qd or Nd.

There is no carry circularity. Since B>=2 is a literal coordinate shift,
the already proved exact powers give `N>=2^K` and `q>=2^(4R^2)` before
any binomial is interpreted. For the one exact binomial and 0<=j<=t,

    binom(F^2+t,j)<=(F^2+t)^t
      <=(R^2+R)^t<=2^(2Rt)<2^(2R^2)<q.

Hence its digit really gives B=binom(F^2+t,t). The ceiling rows then
force F>0 and, by the inherited square-radius fixed-point theorem,
F=t!. The remaining range-digit bounds, reciprocal pairwise-coprime
moduli and amplified prime-power CRT now follow in exactly the order
proved in `inherited/MODULAR_PROOF.md`, Sections 6-7. Those unbounded
proofs are retained, not inferred from sample calculations.

## 7. Complete existence equivalence

At a natural zero, Sections 3-6 first identify the cap, all fifteen
indices, the six powers, the exact factorial binomial, F=t!, and every
range graph. The unchanged amplified CRT and Horn-flow argument decodes
a valid finite C222 refutation. The named inherited calibration gives
ZFC refutability.

Conversely choose a finite calibrated C222 refutation. The inherited
construction chooses a sufficiently large padded horizon t, the true
factorial, beta parameters, positive CRT representatives, all exact
semantic powers and their low digits. Those data determine the enlarged
W before any private Pell witness is selected. Section 3 chooses a large
compatible A; Section 4 constructs its cap and all principal pairs;
Sections 5-6 supply every exact-power and modular quotient. Thus the
entire new raw graph has a natural solution. Restoring the finite
arithmetic gates is total over naturals. The old full collection of
indexed-Pell witnesses is unnecessary.

The common source calibration uses
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`, not a simulation
of K215. The fixed C222 constructor polynomials and source coefficient
data are explicitly included. The argument uses finite algebra,
induction, Pell descent, factorials and CRT, all available internally in
ZFC. Negating the two equivalent existential refutation statements
gives the stated unsolvability/consistency equivalence.

## 8. Finite polynomial compilation and verification boundary

The semantic graph has 777 coordinates and 725 quadratic rows.
Independent replay of every nonnegative affine substitution restores
428 deleted coordinates and yields the supplied 349-coordinate raw
quadratic graph. The balanced natural projection then removes 109 more
coordinates, yielding 240 coordinates and 188 rows. The 239 companion
uses 110 such removals. Every restoration is supplied, including exact
rational sum-of-squares proofs where nonnegative coefficients alone do
not establish nonnegativity.

`verify.py` imports no producer or optimizer. It verifies the unchanged
468-row prefix, every changed semantic suffix row, all fifteen indices,
frame coverage, all six power congruences, all eleven modular requests,
the common-root identity, the adjacent denominator, every affine
restoration, every natural contraction and every collected quartic
coefficient. Deliberately corrupted cap rows, polynomial coefficients
and restoration identities must be rejected. Normal and optimized
Python modes enforce the same obligations through explicit exceptions.

These finite checks establish the exact arithmetic syntax and
polynomial-preserving transformations. They do not prove an unbounded
theorem by testing examples, decide consistency, or stand in for the
inherited logical calibration.
