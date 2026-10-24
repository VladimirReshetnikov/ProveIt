# Independent review of the 23-integer equation of degree 12

## Verdict and scope

The construction is a sound composition of the source-75 signed-power
bootstrap, source-71 determinant guard, source-68 simultaneous-positivity
lemma, and exact integer-polynomial coordinate eliminations. It yields one
fixed-coefficient polynomial in 23 unrestricted integer unknowns, with 11
squared residuals and exact degree 12. The finite algebra was independently
reconstructed without importing the producer or its polynomial library.
The semantic statement remains relative to the expressly named ordinary
Pell/compiler/calibration theorems of those repository sources. This review
is not a new end-to-end proof-assistant or object-language ZFC certificate.

## An independent compact specification

The unknowns are

    J,F,alpha,f,h,r,v,tau,eta,y,gamma,o,j,E,c,a,I,u,Z,t,p1,p2,p3.

Here v means `v_scale`, t means `pair_root`, and p1,p2,p3 mean the three
`pair_pos` coordinates in the JSON packet. The six fixed numerals are the
complete source34 tuple beta,K0,MC,MF and the two source71 weights A0,B0.
They are bound to actual integer payloads. In particular,

    beta=2^1064921-1, A0=2^1113, B0=2^666104.

Define polynomial abbreviations

    q=beta J+1, C=q-F-alpha, s=2v+1,
    X=4q u^2, H=4a+3, Delta=a^2+4a+3,
    V=fo-c, k=1-V+jc+hE, zeta=k-eta,
    D=X+ac+gamma H,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    U=A0 F, W=B0 C,
    G=UW-(q-U-W)^2, Bsign=eta zeta,
    Pair=G Bsign-(t^2-G-Bsign+1)^2
           -1-p1^2-p2^2-p3(p3+1).

The final polynomial is the sum of squares of the following eleven
residuals:

1. a-E-s q^3.
2. E-X(a-E).
3. c-eta-k(a-E).
4. tau^2+(2tau-k)E(c-eta)-1.
5. D^2-Delta c^2-1.
6. jc-V-R.
7. (K0 q+X)C-qF-Z(q-1).
8. I-(2r+1)c^2.
9. I^2-Delta(f^2-1).
10. y^2-I^2(y^2-V^2)-1.
11. Pair.

This is a complete fixed-size polynomial recipe. All displayed
abbreviations are substituted expressions; none is another quantified
variable. Every exponent is a fixed nonnegative integer.

## Exact restoration of the source arithmetic

Given a zero of these residuals, restore source75's eliminated coordinates
by the following integer polynomials:

    L=q^2-1, N=q^3, P=k+E(c-eta), C2=c^2,
    F2=f^2, g=y^2-V^2, Baux=I^2,
    X=4q u^2, D=X+ac+gamma(4a+3),
    V=fo-c, zeta=k-eta,
    tau_old=tau+E(c-eta).

All source75 signed40 arithmetic rows then vanish. Precisely twelve of
its twenty-two arithmetic rows become zero polynomial identities; the
other ten are exactly the first ten residuals above, up to harmless signs.
This is checked over the full symbolic integer coefficient ring, with the
six fixed ports treated as independent parameters during the identity
check. No numerical substitutions are used for these identities.

The shear of tau is essential. With P-k=E(c-eta), the identity is

    (tau+P-k)^2-P^2+Pk-1
      =tau^2+(2tau-k)E(c-eta)-1.

It is an invertible shear over the integers and makes the low-degree
elimination of P possible.

## The merged positivity guard

For arbitrary integers x,y,t, let

    g(x,y,t)=xy-(t^2-x-y+1)^2.

Then x>0 and y>0 if and only if some integer t makes g(x,y,t)>0.
For soundness, g>0 first gives xy>0. If x=-a,y=-b with a,b>=1, then
(t^2+a+b+1)^2>ab, contradiction. For completeness, put N=x+y-1>=1
and choose the nearest square t^2 to N by the integer recipe in source68.
Its squared error is strictly less than N; since xy>=N, g>0.

The positive integer polynomial

    Pos(p1,p2,p3)=1+p1^2+p2^2+p3(p3+1)

represents every positive integer. Indeed 4n-3 is positive and is not of
Legendre's forbidden form; a three-square representation has exactly one
odd coordinate and two even coordinates, giving the displayed formula.
Consequently Pair=0 is equivalent to the conjunction G>0 and eta*zeta>0.
It imposes no sign restriction on the four new witness coordinates.

## The determinant guard is compatible with source75

The source71 guard is

    G=UW-(q-U-W)^2, U=A0 F, W=B0 C,

with fixed A0,B0>=2. If G>0, U and W have the same nonzero sign. Moreover

    |q|>(|U|+|W|)/2>=|F|+|C|.

Thus q,F,C,alpha=q-F-C have one common nonzero sign. In particular both
F*alpha and F*C are positive. Together with eta*zeta>0, the three old
source75 Pos rows can be restored using independent Pos representations.
The preceding exact restoration therefore gives a source75 signed40 zero,
which is sound by its inherited signed-power and compiler theorem.

Completeness must use canonical witnesses, rather than all source75
solutions. The required canonical properties are compatible. Source34's
coefficient proof, section `Canonical parity promises and signed-family
transfer`, states that d,w_c,h_c,N are odd, that q=2^(dN), and that the
rank-tuned canonical R is 3 modulo4. The source71 leading-cell proof
explicitly permits the rank-tuning dummy changes and every canonical
rectangle size; the highest anchors and its determinant estimates are
unchanged. It therefore gives G>0 on these same canonical source34
witnesses. Source75's change to u and cleared transport Z changes none of
J,F,alpha,C. Thus source71's determinant condition survives that change.
Finally choose t and the three Pos coordinates by the universal pair
lemma. The integer-polynomial projections and tau shear above supply the
remaining new coordinates. This proves completeness without assuming an
unproved intersection of two unrelated families of canonical witnesses.

## Exact degree and dimensions

In the displayed order the residual degrees are

    4,4,3,4,6,4,4,3,4,6,6.

There are exactly 23 live unknowns. The full symbolic sum of squares has
16,360 monomial terms when the fixed ports are left symbolic. The
coefficient of eta^4*j^4*c^4 is exactly +1, with no port-dependent
contribution. Hence the final polynomial has degree exactly12 after the
actual fixed integers are substituted. The monomial comes from the square
of the -(eta*zeta)^2 part of Pair after zeta=1-fo+c+jc+hE-eta.

The main Pell residual grows only to degree6 when D is eliminated through
D=4qu^2+ac+gamma(4a+3); the auxiliary residual grows only to degree6 when
V is eliminated through fo-c. These are the two eliminations that turn the
25-variable degree12 presentation into the23-variable presentation.

## Independently executed verification

`audit_integer23.py PATH_TO_INTEGER_PACKET` reads the source and candidate
JSON as inert data and uses its own small AST parser and sparse polynomial
ring. It imports no producer code. It verifies:

- all source arithmetic restorations and the tau shear;
- equality of all eleven final residuals with the compact formulas;
- the unrestricted integer domain, variable list and liveness;
- full symbolic expansion, degree12 and the coefficient+1 witness;
- every supplied fixed-integer payload hash and the three literal powers;
- the whole tuple's mask interval 0<MC<beta<MF<2beta.

The audit passes. The accompanying JSON records the result. These finite
checks certify the literal arithmetic construction; the universal
positivity, canonical cone, signed Pell and syntactic consistency
arguments are the separate mathematical proofs described above and in
the named upstream sources.
