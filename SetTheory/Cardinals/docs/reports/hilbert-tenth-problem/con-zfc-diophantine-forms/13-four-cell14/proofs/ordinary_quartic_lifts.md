# Ordinary-strong quadratic lifts

## Result and provenance

The ordinary-strong Start-only system admits a lift to **24 quadratic
equations in 33 strictly positive integer unknowns**. Its sum of squares
is one polynomial of exact degree four. This improves the 34-positive-
unknown, 25-quadratic lift in package 08 of the pinned repository.

Two unrestricted-integer consequences are supplied:

* 37 quadratic equations in 72 integer unknowns, or their quartic sum of
  squares;
* 24 degree-at-most-four equations in 59 integer unknowns, or their
  degree-eight sum of squares.

These are comparisons within the eight supplied packages, not claims of
global minimality. Classical universal constructions are a separate
comparison class.

The inputs are the ordinary strong-Pell interface of package 02 and the
quadratic lift of package 08, with any coefficient tuple for which the
Start-only compiler theorem holds. In particular the raw-K215 coefficient
tuple of package 06 is admissible. The four coefficients are

    beta = B-1, K0, MC, MF.

The last symbol denotes the **shifted** high-mask port. These are fixed
integer coefficients; they are not quantified unknowns. Source pin:
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`, under
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`:

* `02-system63/PELL_INTERFACE_LEMMAS.md`;
* `06-blank67/proofs/fixed_blank_67_proof.md`;
* `08-start-only67/evidence/diophantine_zfc_encoding/start_only_quartic34_proof.md`.

The decisive change is replacing the scaled root `I=i Delta c^2` by the
ordinary root `I=i c^2`. The register `K=D^2-1=Delta c^2` in package 08 is
then used only by the main Pell equation, so it can be eliminated.

## The 24 equations

The fifteen original unknowns are

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.

The eighteen register unknowns are

    N,E,P,c,a,X,D,C2,G,L,R,F2,V0,V,g,I,Baux,Delta.

For this presentation all 33 unknowns are strictly positive. Use the
affine abbreviations

    q=beta J+1, k=eta+zeta, H=4a+3, C=q-F-alpha.

The equations are

1. `L=q^2-1`.
2. `N=q(L+1)`.
3. `X=wq`.
4. `a=E+sN`.
5. `E=X(a-E)`.
6. `c=k(a-E)+eta`.
7. `P=E(c-eta)+k`.
8. `tau^2=P(P-k)+1`.
9. `D=X+ac+gamma H`.
10. `Delta=a^2+H`.
11. `C2=c^2`.
12. `D^2-Delta C2=1`.
13. `k=R+1+hE`.
14. `G=(q-1)(q-F)+alpha`.
15. `R=LG+(MC+qMF)J`.
16. `(K0+w)C+(q-F)-z(q-1)=1`.
17. `F2=f^2`.
18. `V0=Tf-1`.
19. `V=cV0-RF2`.
20. `g=y^2-V^2`.
21. `I=i C2`.
22. `Baux=I^2`.
23. `Baux=Delta(F2-1)`.
24. `y^2-Baux g=1`.

Every displayed residual has total degree at most two after expanding
the affine abbreviations. Fixed coefficients have degree zero. There is
no variable exponentiation, inequality, divisibility abbreviation, or
unbounded conjunction in the actual system.

Let `r_j` be the displayed left side minus right side and set

    Q33(v)=sum_{j=1}^{24} r_j(v)^2.

Over integers this sum vanishes exactly when all 24 equations hold.
Its degree is exactly four: `tau` occurs in equation 8 alone, with
coefficient 1 on `tau^2`, so the coefficient of `tau^4` in `Q33` is 1.
For a nonnegative domain replace all variables by `n_j+1`, preserving
the count and degree.

## Projection to the ordinary-strong system

Equations 1-6 give, with `Y=a-E`,

    N=q^3, X=wq, Y=sq^3, E=XY, a=E+Y, c=kY+eta.

Equation 7 gives `P=EkY+k`. Therefore equation 8 is the first Pell norm

    tau^2-(XY^2)(XY^2+1)k^2=1.

Equations 9-12 give the main norm

    D=X+ac+gamma(4a+3),
    Delta=a^2+4a+3,
    D^2-Delta c^2=1.

Equations 13-16 give the index and transport equations. In particular

    G=q(q-F)-C,
    R=(q^2-1)G+(MC+qMF)J.

Equations 17-23 give

    V=c(Tf-1)-Rf^2,
    I=i c^2,
    I^2=Delta(f^2-1).

Finally equations 20 and 24 give

    Delta(f^2-1)(V^2-y^2)+y^2=1.

These are exactly the six ordinary-strong Start-only comparisons. Thus
every positive solution of the lifted system projects to a solution of
that system.

## Positive extension of each source solution

All eighteen register values are uniquely determined by the fifteen
original coordinates. Their explicit formulas are precisely those in
the preceding projection proof; hence they satisfy all 24 equations.
Their positivity must be justified, because adding positive register
variables is otherwise a potential restriction.

The only non-immediate cases are `G,R,V0,V,g`. First, the transport
equation implies `C>0`: if `C<=0`, then

    (q-F)-z(q-1)=1-F-(z-1)(q-1)<=0,

so its left side cannot be 1. Consequently `q-F=C+alpha>0` and `G>0`.
The native index expression then gives `R>0`.

The first norm, main norm, ratio, and index equations give the same
prefix estimates as in package 06 before its strong-norm step:

    A=a+2, Delta=A^2-1,
    c=psi_A(p), p>n>=24, c>A Delta^2,
    0<R<a<Delta.

Apply package 02's ordinary strong-Pell lemma to
`(i c^2)^2=Delta(f^2-1)`. It supplies

    f=chi_A(m), p|m, c|m, m>=c>2p.

In particular `f>2c` and `f^2>Delta+c`. One way to see the first
inequality is to use Pell addition and monotonicity:
`chi_A(m)>psi_A(2p)=2chi_A(p)c>2c`.
Thus `V0=Tf-1>0`.

Put `Baux=I^2=Delta(f^2-1)`. Then

    Baux-(Rf^2+c)=(Delta-R)f^2-Delta-c>0.

The auxiliary norm is

    Baux V^2-(Baux-1)y^2=1.

It excludes `V=0`. If `v=abs(V)>1`, elementary integer inequalities
give `v>=2Baux-1`: from
`v^2-1=(Baux-1)(y^2-v^2)` one has `abs(y)>=v+1`, and the claimed lower
bound follows. On the other hand `T>0` gives
`V>-(Rf^2+c)>-Baux`. Thus a negative `V` with absolute value greater
than one is impossible. Values `V=+1` and `V=-1` are impossible because
`V=-c mod f` and `f>2c>2`. Hence `V>1`.

Finally

    (Baux-1)g=V^2-1>0,

so `g>0`. All other register values are plainly positive sums or
products, or `L=q^2-1>0`. This proves positive extension and therefore
equivalence of the 33-variable system with the ordinary source.

The source theorem is an ordinary mathematical reduction, not a new
Lean/Rocq theorem. The final assertion about Con(ZFC) additionally uses
the inherited Start-only compiler theorem and K215 calibration.

## Allowing signed roots and signed registers

For the integer-domain improvements it suffices to require positivity
only of the following thirteen original coordinates:

    J,F,alpha,z,f,h,i,T,s,w,eta,zeta,gamma.

Allow `tau,y` and all eighteen registers to range over all integers.
The defining equations still uniquely determine every register. The
projection proof still gives the source equations. The first norm
excludes `tau=0`, because its right-hand product is positive. The
auxiliary norm excludes `y=0`, since that would give `Baux V^2=1`
while `Baux=(i c^2)^2>1`. Replacing `tau,y` by their absolute values
preserves all equations. The positivity proof just given does not
assume signs of `V,g` or the other registers: it proves them from the
thirteen positive original coordinates. Hence the enlarged integer
domain adds no projected solutions.

## An explicit quartic in 72 unrestricted integer unknowns

Every positive integer has a representation

    Pos(u,v,t)=1+u^2+v^2+t(t+1), u,v,t in Z.

The form is always positive. Conversely, for `n>=1`, the integer
`4n-3` is 1 modulo 4 and is therefore not of the excluded form
`4^a(8b+7)` in Legendre's three-square theorem. In a three-square
representation it has exactly one odd square. Write that square as
`(2t+1)^2` and the other two as `(2u)^2,(2v)^2`; division by four
gives `n=Pos(u,v,t)`.

Keep all 33 coordinates as unrestricted integers. For each of the
thirteen original coordinates required positive, introduce a fresh
triple `(u_x,v_x,t_x)` and the quadratic equation

    x=1+u_x^2+v_x^2+t_x(t_x+1).

There are `33+3*13=72` unknowns and `24+13=37` quadratic equations.
The sum of their squared residuals is an ordinary polynomial of exact
degree four. Its integer zeros correspond exactly to source solutions,
by the signed-root/register observation and the positivity theorem.
The coefficient of `tau^4` remains 1.

## A degree-eight polynomial in 59 unrestricted integer unknowns

Instead substitute `Pos(u_x,v_x,t_x)` directly for each of the thirteen
positive original coordinates in the 24 residuals. The thirteen
coordinates disappear and 39 coordinates replace them, leaving
`33-13+39=59` unknowns. Each substituted residual has degree at most
four, so its sum of squares has degree at most eight.

The degree is attained on every valid coefficient slice. The first
residual is `L-((beta J+1)^2-1)`. After substitution it contains the
term `-beta^2 J_pos_u^4`. Since `beta>0`, at least one leading quartic
form is nonzero. A sum of squares of real quartic forms cannot vanish
identically unless each form does. Thus the sum has exact degree eight.

## Executable algebra audit

`code/quartic33.py` uses only Python's standard library and implements
integer sparse-polynomial arithmetic. It checks:

* all 24 literal residuals have degree at most two;
* all eighteen defining residuals vanish identically after substitution;
* the six remaining residuals equal the ordinary source comparisons,
  with exact degrees 22,18,7,2,22,28;
* the positive/natural quartic has coefficient 1 on `tau^4`;
* the integer variants have the stated counts and degrees.

Run `python3 code/quartic33.py` to regenerate the data in memory and
compare it with `data/quartic33_verified.json`. Add `--write` to replace
that JSON with an exact regeneration. The JSON contains every expanded
integer-coefficient residual for all three variants. The test is an
algebra and bookkeeping audit; it does not claim to prove the inherited
Pell or compiler results by finite sampling.
