# A symmetric four-root norm and three smaller integer evaluators

Research date: 24 October 2026. Comparison commit:
`84e16e43092614bae262ca59651cb9d77e31a255` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).

## 1. Result and precise scope

We give the following exact arithmetic-circuit replacements.

| Equation | Unrestricted integer unknowns | Exact degree | Parent operations | New operations |
|---|---:|---:|---:|---:|
| Quadratic trace | 13 | 536 | 135 | **127** |
| Rational scalar carrier | 12 | 1200 | 145 | **139** |
| Integral scalar carrier | 12 | 1456 | 141 | **138** |

An operation is one live binary addition, subtraction, or multiplication;
multiplication by an integer is charged. Constants and reuse are free.
This measures the division-free evaluator, not expanded coefficient height
or bit complexity. All coefficients are fixed integers, supplied literally
as six authenticated compressed byte strings. All powers in the resulting
polynomials have fixed nonnegative integer exponents.

Each new evaluator computes **exactly the same polynomial at every integer
assignment** as its pinned parent. In particular its domain, integer zero
set, expanded coefficients, exact degree, and arithmetic/refutation
calibration are unchanged. The only new mathematical ingredient is a
universal polynomial identity. The stronger 135-to-127 reduction also
shares the common factor delta*U^2 before evaluating three radicands.

Under precisely the parents' named native-compiler/refutation calibration,
each equation therefore retains the ordinary theorem formalizable in ZFC:

    there is no integer zero  <=>  Con(ZFC).

No new formalization of that full calibration in Lean or in the repository's
object-language ZFC calculus is asserted. The new identity itself is
elementary ring algebra. We neither prove consistency nor claim a global
minimum or worldwide priority. This is a concrete circuit improvement over
the inspected source checkpoint, not a reduction in the number of variables.

## 2. The 29-operation four-root norm

Let

    F16(x;a,b,c,d)
      = product_(epsilon in {-1,+1}^4)
          (x-epsilon1*sqrt(a)-epsilon2*sqrt(b)
             -epsilon3*sqrt(c)-epsilon4*sqrt(d)).

Changing the sign of any root permutes the factors. Therefore F16 is an
ordinary polynomial with integer coefficients in x,a,b,c,d, and it is even
in x. Write N4(z;a,b,c,d)=F16(x;a,b,c,d) with z=x^2. Define

    p=a+b, q=c+d, u=ab, v=cd,
    e1=p+q,
    e2=u+v+pq,
    e3=uq+vp,
    e4=uv,
    s=z-e1,
    t=s^2-4e2,
    C=t^2+64(e4-z e3),
    L=t-4zs.

Then the identity is

    N4(z;a,b,c,d) = C^2 - 256 e4 L^2.                   (1)

The four elementary symmetric polynomials cost twelve binary operations
in the displayed schedule: four for p,q,u,v, one for e1, three for e2,
three for e3, and one for e4. The remaining schedule costs seventeen:
one for s, three for t, five for C, three for L, and five for the final
expression. Thus the norm costs **29 operations when z=x^2 is supplied**,
or 30 when x itself is supplied. The numerals 4,64,256 are fixed leaves.

### Algebraic proof without a division at a special value

Work first over the polynomial ring in four algebraically independent
symbols r1,r2,r3,r4 over the rationals. Set a_i=r_i^2 and
x=r1+r2+r3+r4. Let p2,p3,p4 be the elementary symmetric expressions of
degrees 2,3,4 in the r_i. The elementary identities are

    2p2=x^2-e1=s,
    e2=p2^2-2xp3+2p4,
    e3=p3^2-2p2p4,
    e4=p4^2.

Consequently

    t+8p4=8xp3,
    p3^2=e3+s p4.

Square the first equality and substitute the second:

    t^2+64(e4-x^2 e3)+16p4(t-4x^2 s)=0.

Thus C+16p4 L=0, which implies (1) vanishes at x=r1+r2+r3+r4.
The identical argument applies to each of the sixteen independent sign
choices. For algebraically independent r_i these sixteen roots are distinct.
Both sides of (1), regarded as polynomials in x, are monic of degree 16.
They are therefore equal over the rational-function field in the r_i,
and hence as polynomial identities. Specialization gives the identity over
every commutative ring. No division by x, a radicand, or a discriminant occurs,
so zero radicands and coincident specialized roots cause no exception.

The supplied independent sparse-polynomial checker also multiplies all
sixteen signed linear factors directly. After cancellation it obtains all
495 coefficients and compares them with (1); it does not infer this identity
from sampled evaluations.

## 3. Denominator clearing without rational arithmetic

Homogeneity gives the polynomial identity

    delta^8 F16(Z;A,B,E,Cn/delta)
       = N4(delta Z^2;delta A,delta B,delta E,Cn).       (2)

One may derive it for nonzero delta in a field extension by scaling every
root by sqrt(delta). Because both sides after clearing denominators are
integer polynomials, it holds identically, including delta=0. Formula (2)
is particularly useful computationally: the right side uses only integer
addition, subtraction and multiplication and calls the same 29-operation
norm. The identity does not impose positivity on delta or any radicand.

If A=U^2 Df, B=U^2 Dt, E=U^2 Ag and Cn=U^2 Cy, form

    D=delta U^2,
    a'=D Df, b'=D Dt, c'=D Ag, d'=U^2 Cy,
    z'=delta Z^2.

This shares D and eliminates two multiplications relative to separately
forming the three U^2-scaled radicands and then multiplying each by delta.
Together with the symmetric norm this saves eight operations in trace13.

## 4. Complete thirteen-integer specification

The unknowns are exactly

    j,C,z,h,r,v,w,T,c,n,t,p2,p3 in Z.

The fixed coefficient names beta,K0,MC,MF,Acone,Bcone mean the entire
`mixed-parity-unrounded-1064921` tuple in coefficients/BINDING.json.
There are no coefficient unknowns. In particular beta=2^1064921-1,
Acone=2^1113 and Bcone=2^666104. MF is already shifted once by beta.
The other three exact numerals are fixed by the authenticated compressed
little-endian payloads; all six must be used together.

Define the following polynomial abbreviations:

    J=6j+1, q=beta J+1, W=12w+4, X=qW, Y=qv, E=XY,
    a=E+Y, H=4a+3, Delta=a^2+H,
    F=(K0+W)C-z(q-1),
    R=[q(q-F)-C](q^2-1)+(MC+q MF)J,
    k=R+1+hE, eta=c-Yk, zeta=k-eta,
    i=2r+1, I=ic^2, Df=1+Delta I^2,
    Q=Delta^2 I^2, delta=Q-1,
    V=Df(cT-R)-c, Cy=QV^2-1,
    ell=XY^2, L0=ell k, Dt=1+L0(L0+k),
    G=(Acone F)(Bcone C)-(q-Acone F-Bcone C)^2,
    Pair=G eta zeta-(t^2-G-eta zeta+1)^2,
    Ag=Pair-1-p2^2-p3(p3+1),
    M=2q^2, U=MH,
    K=X(X+2ac)-1,
    Z=U(n+V)+MK+H(v-q^2),
    D=delta U^2.

The complete new equation is

    N4(delta Z^2; D Df, D Dt, D Ag, U^2 Cy)=0.         (3)

N4 is defined by the explicit 29-operation formula (1), not by an
uncomputed resultant or hidden variable. Consequently (3) is one ordinary
integer polynomial in precisely the stated thirteen variables. The literal
division-free DAG is symmetric_trace13.json.

By (2), (3) is the parent's polynomial
delta^8 F16(Z;U^2 Df,U^2 Dt,U^2 Ag,U^2 Cy/delta), identically.
Its exact degree 536 transfers from that polynomial. In particular the
parent's proved positive coefficient is unchanged:

    [j^240 w^80 v^96 h^16 r^32 c^64 z^8] P
       = 2^488 3^320 beta^240 > 0.

The exponent sum is 536. The new evaluator has 73 multiplications,
28 additions, and 26 subtractions, all live. The unchanged prefix through
node 115 accounts for every front abbreviation. The independent checker
then binds the entire remaining tail over a free polynomial ring; a finite
list of numerical examples is not used as the proof of equality.

## 5. Twelve-integer companions

The two literal parent specifications and their complete ordinary proof
are retained. Their twelve coordinates are

    j,C,z,h,r,v,w,T,c,n,t,s in Z.

They use the same six fixed coefficient bytes, verified independently from
both original bindings. Their complete common front is unchanged through
node 124 of the retained parent files. In the notation of the copied proof,
S is the scalar carrier scale, Z its center, and Df,Dt,Dg,Cy,delta the
four radicand data. The two new equations are exactly

    N4(delta Z^2;
       9 delta S^2 Df,81 delta S^2 Dt,729 delta S^2 Dg,S^2 Cy)=0,

and

    N4(Z^2;
       9 S^2 Df,81 S^2 Dt,729 S^2 Dg,S^2 delta Cy)=0.

Every front abbreviation is literal in the two delivered JSON circuits;
their meanings, signed soundness and witness construction are supplied by
the copied scalar-carrier12/PROOF.md and its inherited interface proofs.
Identity (2) proves the rational companion is pointwise equal to its parent;
identity (1) proves the integral companion is pointwise equal to its parent.
The exact degrees 1200 and 1456, respectively, are unchanged. Their counts
are (86 multiplications,28 additions,25 subtractions) and
(85 multiplications,28 additions,25 subtractions).

These companions make a different tradeoff from the thirteen-variable
127-operation form: they save one unknown, while increasing degree and
evaluation cost. They do not improve the repository's separate ten-integer
Sun endpoint or its positive-domain equations in every complexity measure.

## 6. Reproduction and evidence boundary

Run, with Python 3 and no third-party packages:

    python3 norm_identity.py
    python3 build_symmetric_trace13.py
    python3 build_symmetric_scalar12.py
    python3 verify_symmetric_norms.py

The verifier imports neither producer. It checks the free-ring norm identity,
the exact unchanged source prefixes, all 495 coefficients of each complete
old/new norm tail, graph topology, liveness, variable inventories and exact
operation counts. It decompresses all six fixed numerals and checks their
raw byte hashes, bit lengths, byte counts and stated power-of-two recipes.
It authenticates every retained source file by SHA-256 and Git blob identity.
It also performs 300 actual-coefficient modular controls per endpoint;
these controls supplement, rather than establish, the universal identities.

The receipt is VERIFICATION.json. SOURCE_PINS.json names immutable upstream
files. The original upstream license is retained. The mathematical proof of
the new norm identity is complete here. The much larger inherited
native-compiler/refutation equivalence is identified and copied to the
extent listed in SOURCE_PINS.json; this packet is not a new end-to-end
formal certificate for that dependency.

## 7. Directions deliberately not promoted to theorems

A tempting way to lower the thirteen-integer endpoint to twelve integers
is to replace its additive three-square guard by a single Pell guard and
absorb the guard's nonzero ordinate into the trace carrier. The simple
carrier U=sMH fails to exclude s=0 automatically; adding an intersective
polynomial returns the degree costs already present in scalar-carrier12.
No new twelve-variable trace theorem was proved in this investigation.
The delivered results are the exact evaluator reductions above.
