# Fifteen positive variables, degree 44, and 76 arithmetic operations

## What is new, and what is inherited

The deliverable is a smaller evaluator for the already known degree-44
positive-variable construction. It uses **15 strictly positive integer
unknowns, one polynomial equation, degree 44, and 76 binary arithmetic
operations** (41 multiplications, 19 additions, 16 subtractions).

Both Pell-root gap substitutions are already in historical package 15,
`POSITIVE_GAP_SHEARS.md`, at the wave-2 pin `5b0c9ae9fd`. Package 12 already
gave a degree-44, 78-operation sum of squares using the auxiliary gap alone.
Package 10 gave the 74-operation, degree-56 polynomial Q56 using four grouped
residuals. The present contribution combines these ingredients and changes
which norm is paired with which index/transport unit. It saves two
operations over the earlier degree-44 evaluator; it is not a new minimum
variable-count theorem, the first degree-44 construction, or an operation
record below P67.

The historical Q56 comparison has been checked against its actual
`ordinary_blank_four_sos_74.json` and `sections/ordinary_section.tex`, not
just a catalogue entry. Its domain is precisely fifteen strictly positive
integers, its degree is 56, and every binary addition, subtraction or
multiplication, including by a fixed numeral, costs one. It uses the
ordinary strong equation and inherits the same compiler/strong-rank proof
boundary as this construction. The old fixed coefficient tuple differs;
the displayed algebraic templates may both be rebound as whole tuples to
the authenticated package-31 compiler. No polynomial identity across
different coefficient tuples is asserted.

## Coefficients and exact equation

Use the complete package-31 tuple `wang943-mixed-121x8801`, with
`B=2^1064921`, from the repository at
`124c07c0b77a9e20e84676514d8b1ff78536ea3f`. Its ports are

    beta = B-1, K0 = DC+B*DR, MC, MF = MF_native+B-1.

MF is already shifted. The four ports must be replaced together. The
source evaluator copied in `upstream/p69_unscaled.json` is an algebraic
template whose original package-36 binding is not carried over. The final
`offset44.json` explicitly rebinds all four ports to package 31. This is a
different fixed polynomial from the active package-36-bound Lean object.

All fifteen variables are strictly positive integers, in this order:

    J,F,alpha,z,f,h,i,T,s,w,r,eta,zeta,u,gamma.

The letters below are polynomial abbreviations, not additional witnesses:

    q = beta*J+1, C = q-F-alpha,
    X = w*q, Y = s*q^3, E = X*Y,
    k = eta+zeta, c = k*Y+eta, a = E+Y,
    H = 4*a+3, Delta = a^2+H,
    D = X+a*c+gamma*H, L = E*k*Y,
    G = (q-1)*(q-F)+alpha,
    R = G*(q^2-1)+(MC+q*MF)*J,
    V = c*(T*f-1)-R*f^2,
    A0 = Delta*(f^2-1), I = i*c^2.

Define

    N0 = r^2+L*(2*r-k),
    N1 = D^2-Delta*c^2,
    Na = (V+u)^2-A0*u*(2*V+u),
    Nk = k-h*E-R,
    Nt = (K0+w)*C+(q-F)-z*(q-1).

The single equation is

    (N0*Nk-1)^2+(N1*Nt-1)^2+(Na-1)^2+(I^2-A0)^2 = 0.       (Q44)

Only fixed nonnegative exponents occur, and the division-free literal DAG
includes every operation used to compute these abbreviations.

## Inherited interface, stated explicitly

For an authentic whole blank-K215 compiler tuple, the ordinary strong-norm
source uses the same core abbreviations, but supplied positive roots
`tau,y`, and the factors

    N0_old = tau^2-L*(L+k),
    Na_old = A0*(V^2-y^2)+y^2,
    Ns_old = 1+I^2-A0.

Its positive six-equation presentation is

    N0_old=N1=Na_old=Nk=Nt=1, I^2=A0.                       (S)

The inherited ordinary compiler theorem proves that existence of a positive
solution of (S) is equivalent to blank K215 halting. This interface requires
the ordinary strong-rank theorem: one must not divide an arbitrary supplied
`i` by Delta. Its proof is reproduced in package 36's
`INHERITED_ORDINARY_PROOF.md` and package 31's
`sources/ORDINARY_BLANK_PROOF.md`. Package 31's coefficient proof validates
this whole tuple for that compiler interface. The K215 calibration identifies
blank halting with a finite ZFC refutation.

For completeness it is enough to use the normalized canonical witness.
Replacing its strong multiplier by `i_ordinary=Delta*i_normalized` gives
(S). At that witness `V>1`, `y>0`, `A0>1`, `tau>0`, and all six equations
hold. The strict bound V>1 is essential here: V=y=1 would give gap u=0.
The normalized proof excludes V=0 by the auxiliary norm and V=+/-1 by
`V=-c mod f` together with `f>2c>2`. Its auxiliary inequalities exclude
negative V, hence V>1. These are explicit inherited facts, not an inference
from a finite search.

## New reduction: complete soundness and positive completeness

The two exact polynomial identities are

    (L+r)^2-L*(L+k) = r^2+L*(2*r-k),

    A0*(V^2-(V+u)^2)+(V+u)^2
      = (V+u)^2-A0*u*(2*V+u).                              (1)

Assume (Q44) has a positive integer zero. A sum of four integer squares
vanishes only when all four residuals vanish. Thus

    N0*Nk=1, N1*Nt=1, Na=1, I^2=A0.

In particular N0 and N1 are integer units. Put `tau=L+r>0`. Since
`L=XY^2*k`, the first identity writes

    N0=tau^2-n*(n+1)*k^2, n=XY^2>=2.

The consecutive-product negative Pell obstruction excludes N0=-1. To
recall its elementary proof, if
`x^2-n(n+1)t^2=-1` with n>=2 and t>0, then
`nt<|x|<(n+1/2)t`. The new second coordinate
`t'=(2n+1)t-2|x|` is an integer strictly between 0 and t. Multiplication
by the norm-one unit `2n+1-2*sqrt(n(n+1))` gives another norm-minus-one
solution with second coordinate t', contradicting the smallest positive
second coordinate. Therefore N0=Nk=1.

Also `Delta=(a+2)^2-1` is 0 or 3 modulo 4. For either residue, a number
`D^2-Delta*c^2` cannot be 3 modulo 4. Hence N1 is not -1, so N1=Nt=1.
Unlike grouping all three remaining factors together, this pairing forces
both index and transport signs directly. In particular the ordinary source
may start with its exact transport equation and C>0.

Let `y0=V+u`. From the second identity, Na is exactly the old auxiliary
factor at y0. If y0=0, Na=1 would give `I^2*V^2=1`. But `i>=1` and
`c=kY+eta>1`, so `I=i*c^2>1`, a contradiction. Thus `y=|y0|>0`.
The old source depends on y only through y squared. All of its other
coordinates remain positive. Together with restored tau, these values
therefore solve (S), and the inherited compiler proves blank halting.
No positivity of the untested expression V+u was assumed.

Conversely, take a canonical normalized blank-halting witness and transfer
it to (S) by `i_ordinary=Delta*i_normalized`. Define

    r=tau-L, u=y-V.

The first norm gives `tau^2-L^2=L*k+1>0`; since tau,L>0, r>0. The
auxiliary norm gives

    (A0-1)*(y^2-V^2)=V^2-1>0.

Since A0>1 and V,y>0, this implies y>V and u>0. Identities (1) preserve
the two norm equations; all the other equations are untouched. Hence
(Q44) vanishes with all fifteen coordinates positive.

This proves positive existence equivalence to the authenticated source.
Composing the elementary arithmetic, inherited compiler, and K215
calibration gives the ordinary mathematical theorem formalizable in ZFC:

    ZFC proves: (Q44 has no positive integer zero) iff Con(ZFC).

This is not an assertion that consistency or inconsistency is established,
and it is not a newly checked object-language ZFC derivation. No new
Lean/Rocq compilation is claimed.

## Exact degree and operation certificate

Let Q=beta*J, k0=eta+zeta denote highest-degree parts. Then

    deg(c)=5, deg(a)=6, deg(V)=7, deg(A0)=14, deg(I^2)=22.

The first gap norm has degree 12. The main norm has degree 18 by the
exact cancellation, with Z=X+gamma*H,

    (a*c+Z)^2-(a^2+H)*c^2 = Z^2+2*a*c*Z-H*c^2.

The auxiliary gap norm has degree 22. Nk and Nt have degrees 7 and 2.
The four residual degrees in (Q44) are therefore 19,20,22,22. Their
squared sum has degree at most 44. Its highest homogeneous part is

    i^4*k0^8*s^8*Q^24
      +4*k0^2*w^4*s^6*T^2*f^6*u^2*Q^22.

The coefficient of `i^4*eta^8*s^8*J^24` is beta^24, nonzero for this
tuple. Other residuals are independent of i and cannot cancel it. Thus
degree 44 is exact, not just an upper envelope.

`offset44.json` contains exactly 76 live binary gates. In the listed
evaluator the auxiliary gap uses the already computed sum `V+u`, and
computes `2V+u` as `V+(V+u)`. The first gap uses `2*r-k`. The six
norm/index/transport producers, the two pair products, the four residuals,
four squares, and three additions are all fully charged. The independent
audit reports 41 multiplications, 19 additions and 16 subtractions; all
fifteen witnesses and all four fixed coefficient ports are live.

Run from this directory:

    python3 build_offset44.py
    python3 audit_offset44.py
    python3 -O audit_offset44.py

The audit verifies DAG dependencies, liveness, operation counts, the three
exact polynomial identities, the complete leading homogeneous form, and
the nonzero distinguished coefficient. Eighty independent full-formula
evaluations and 106 elementary Pell examples are diagnostics only. They
are not evidence for consistency, nor do they replace the semantic proof.

## Historical source ledger

All paths below are under
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/`
at historical commit `5b0c9ae9fd`:

- `10-synthesis14/sections/ordinary_section.tex`: Q56, its four equations,
  positive domain, 74-operation count, and ordinary strong-rank proof.
- `10-synthesis14/circuits/ordinary_blank_four_sos_74.json`: literal Q56 DAG.
- `12-gap-norm14/proofs/GAP_AUXILIARY_PROOF.md`: auxiliary gap and earlier
  degree-44, 78-operation sum of six squares.
- `12-gap-norm14/arithmetic/ordinary_gap_sos78.json`: its literal DAG.
- `15-release/evidence/diophantine_zfc_round2/pell/POSITIVE_GAP_SHEARS.md`:
  both gap substitutions, the 71-operation degree-83 product, and the
  earlier 80-operation degree-44 six-square evaluator.

The bounded audit did not identify an earlier 76-operation degree-44
evaluator. This is a repository comparison at specified pins, not a global
priority or minimality claim.
