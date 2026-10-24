# Coprime Pell saturation in twelve unrestricted integer variables

## Result and precise scope

The polynomial in `rational.json` has **twelve unrestricted integer
variables, 123 live binary arithmetic operations, and exact total degree
1084**. Its zeros exist exactly when the retained native construction has
a witness, hence exactly when there is a finite syntactic ZFC refutation,
under the same ordinary native/compiler/refutation calibration as the
pinned parent. Consequently the retained calibration and the arithmetic
proof below give the ordinary ZFC-provable equivalence

    Con(ZFC)  <=>  for every x in Z^12, P(x) != 0.

This reduction does not itself establish either side of the equivalence.
No new Lean endpoint, complete
encoded object-ZFC derivation, or global minimality claim is made.
The substantial local change is a transfer of coprime Pell saturation to
the signed scalar carrier, with a compatible rescaling of the auxiliary
coordinate. The complete arbitrary-residue interpolation theorem is
essential to the reverse implication.

The retained parent has 145 operations and degree 1200 in its rational
chart, and 141 operations and degree 1456 in its integral chart. The new
123/1084 polynomial improves both metrics at the same twelve-integer
domain. The separate centered 143/1200 and 146/1184 controls remain valid.
An integral chart of the saturation is included for checking; it also has
123 operations but degree 1280, so it is dominated by the rational chart.

## 1. The complete polynomial

The twelve independent variables, each ranging over all of Z, are

    j, C, z, h, r, v, w, T, c, n, t, s.

The six fixed integer coefficients are the exact source34 tuple
`beta,K0,MC,MF,cone_A,cone_B`. Here

    beta = 2^1064921-1, cone_A = 2^1113, cone_B = 2^666104.

`MF` is the already shifted source coefficient. The complete bytes of
every coefficient are in `coefficients/`, with lengths and SHA256 values
in `coefficients/BINDING.json`; no unspecified parameter remains. The
finite recipe `coefficients/recipe/source34_builder.py`, its full tile
table, and the exact `k215.tm` seed reproduce all four large ports. The
whole provenance is pinned to ProveIt commit
`84e16e43092614bae262ca59651cb9d77e31a255` in
`INHERITED_SOURCE_PINS.json`. This construction continues to use that
existing calibrated coefficient family; it is not an independent
replacement of the source compiler or its consistency calibration.

All symbols below are polynomial abbreviations, not extra unknowns.

    J = 6j+1, q = beta J+1, W0 = 12w+4,
    X = q W0, Y = (2v+1)q^3,
    a = (X+1)Y, H = 4a+3, Delta = a^2+H = (a+2)^2-1,
    F = (K0+W0)C-z(q-1),
    R = (q(q-F)-C)(q^2-1)+(MC+q MF)J,
    k = R+1+hXY, eta = c-Yk, zeta = k-eta,
    G = (cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    Pair = G eta zeta-(t^2-G-eta zeta+1)^2,
    Dg = (3Pair-4)s^2+1,
    ell = XY^2, E = 1+ell(ell+1)k^2,
    U = s r c^2,
    Df = 1+Delta U^2 E, Q = Delta^2 U^2 E, delta = Q-1,
    b = c-R+4UET, V = Df b-c, Cy = QV^2-1,
    K = X(X+2ac)-1, S = U H^5,
    zc = HT+K, Ac = (zc^2+3H^2)(zc^3-19H^3),
    Z = S(n+V)-Ac.

Define four squared arguments

    fs = delta Z^2,
    fa = 9 delta S^2 E Df,
    fb = 81 delta S^2 Dg,
    fc = S^2 Cy.

The requested ordinary integer polynomial is

    Pe = (fs+fc-fa-fb)^2-4(fs fc+fa fb),
    P = Pe^2-64 fs fc fa fb.                                  (1)

The literal graph contains only integer constants, the twelve variables,
the six fixed coefficient ports, and binary +, -, * operations. It
computes the weighted guard directly as

    Dg81 = (243Pair-324)s^2+81 = 81Dg,

then uses `fb=delta S^2 Dg81`. This saves one operation and changes no
polynomial. Squaring and every other fixed power in the display are
implemented by counted multiplications in the graph.

For explanation, put

    F8(z;A,B,C) = product over eps in {-1,1}^3 of
                         (z-eps1 sqrt(A)-eps2 sqrt(B)-eps3 sqrt(C)).

Sign invariance makes this an integer polynomial. Formula (1) is exactly

    P = delta^4 F8(Z;9S^2 E Df,81S^2 Dg,S^2 Cy/delta).         (2)

Equation (2) is a mnemonic only: (1), or its 123-operation graph, is the
division-free definition. The displayed denominator has been cleared
symbolically. A proof below shows `delta` is never zero on Z^12.

The integral control replaces `Z` by `S(n+delta V)-Ac` and uses

    fs=Z^2, fa=9S^2 E Df, fb=81S^2 Dg, fc=S^2 delta Cy.

It is the unscaled three-root norm with those integral radicands.

## 2. The inherited interfaces used by the new reduction

The retained files are complete, hash-pinned copies rather than unnamed
dependencies. The exact interfaces used here are:

1. `parent/PROOF.md`, Sections 3--4, and
   `parent/source/signed-quadratic-proof.md`: from the signed front end,
   strict guards, nonzero strong witness `I` with `c^2|I`, square first
   norm `E`, strong norm `f^2=1+Delta I^2`, auxiliary norm
   `Q V^2-(Q-1)y^2=1` with `Q=(Delta I)^2` and
   `V=f^2(c-R+4I T_old)-c`, and `H|K`, the absolute folding and signed
   rank argument restore the omitted main root and generalized signed
   strong kernel. That reviewed kernel has the named ordinary native
   and finite-refutation endpoint.
2. `parent/source/INTERPOLATION12.md`, Section 6: for canonical native
   `A0=a+2>1` even, `R=3 (mod 4)`,
   `c=psi_A0(R)>0`, `c=R (mod 4)`, and **every** positive `N`, there is
   one fixed strong pair `I,f` with `4N c^2|I`, such that **every residue
   class modulo that same I** is attained by an auxiliary `T_old` with
   the displayed auxiliary Pell norm. The strong pair is chosen before
   the requested residue class. The proof uses the squared-modulus period
   `4*m*f`, not the generally insufficient `4*m`.
3. `parent/source/PRIME_TWELVE.md`, Sections 2--3: the quintic
   `pi(x)=(x^2+3)(x^3-19)` is intersective and has no rational zero;
   the prime-order separation argument for square roots is valid.
4. The canonical completeness and positivity witnesses of the same
   parent, including a positive guard witness `s` and an integer
   square root `tau` of the first norm.

The new construction changes the strong and auxiliary coordinates, so
one must check their compatibility with all four interfaces. That is
done explicitly below. There is no claim that the full old scalar
polynomial is obtained by pointwise substitution of the new variables:
its carrier uses `T_old`, whereas the new carrier must use `T`.

## 3. Unconditional signed and zero-case bootstrap

For every integer assignment, `J` is odd and nonzero. Since beta is the
fixed odd number above, `q` is even, `q=2 (mod 3)`, and `|q|>=16`.
The factor `W0=4(3w+1)` is nonzero, so `|X|>=64` and `X=-1 (mod 3)`.
The odd multiplier in `Y` gives `|Y|>=4096`. Therefore `|a|` is large,
`H` is nonzero and odd, and `Delta=(a+2)^2-1>1`.

For every integer `ell`, `ell(ell+1)>=0`; hence `E>=1`.
Also `Df>=1`. If `U=0`, then `Q=0`; if `U!=0`, then
`Q=Delta^2 U^2 E>=Delta^2>1`. Thus **Q cannot equal 1**, and `delta`
is nonzero on every integer assignment, before assuming the equation.

Suppose first that `U=0`. Then `S=0`, `delta=-1`, and both the rational
and integral polynomials reduce exactly to `Ac^8`. It cannot vanish:

    Ac = H^5 pi(T+K/H), pi(x)=(x^2+3)(x^3-19).

The argument is rational, the quadratic factor has no real zero, and
the cubic has no rational zero by the rational-root theorem. Therefore
every zero of either final polynomial has `U!=0`, and consequently
`s,r,c` are all nonzero and `|U|>=c^2`.

Now `Q>1`, and `Df=1+Delta U^2 E>|c|+1`. Since `b` is an integer,
if `b=0` then `|V|=|c|>=1`; otherwise
`|V|>=Df-|c|>1`. Hence `Cy=QV^2-1>0`. The auxiliary radicand and
the product radicand `E Df` are strictly positive before any projection
or guard argument. Only `Dg` might initially be negative.

At a zero, a conjugate factor of (2) vanishes over C. Divide it by the
nonzero real integer `S`, absorbing its sign into the three independent
signs. If `Dg<0`, the guard term is the only nonzero imaginary term,
which cannot sum to a rational number. Thus `Dg>=0`. Because `s` is a
nonzero integer, `Pair<=0` would imply
`Dg=(3Pair-4)s^2+1<=-3`. Therefore `Pair>0`.

This yields the strict guards `G>0` and `eta*zeta>0`. Indeed the
product is positive; if both factors were negative, writing them as
`-A,-B` with `A,B>0` would give
`Pair=AB-(t^2+A+B+1)^2<0`, a contradiction. No assumed sign of `X`,
`Y`, `H`, `c`, or `U` has entered this argument.

## 4. Three-adic separation and coprime saturation

Modulo 3, `X=-1`, so `a=H=Delta=0`. Moreover
`ell=XY^2` is either 0 or -1 modulo 3, and consequently
`ell(ell+1)=0`. Therefore

    E=Df=1, Q=0, delta=Cy=-1 (mod 3).

The three normalized magnitudes in a vanishing rational-chart factor are

    sqrt(Cy/delta), 3sqrt(E Df), 9sqrt(Dg).

Their squared 3-adic orders are respectively `0,2,4+v3(Dg)`.
In the integral chart the first magnitude is `sqrt(delta Cy)` and
again has squared order zero. If `Dg=0`, omit its zero term.

Here is a short form of the separation argument. Distinct square
classes of positive rationals are linearly independent after adjoining
their square roots. In a rational signed sum, the terms in each
nontrivial square class would have to cancel among themselves. Within
any such class the ratios of roots are rational, and the displayed
distinct valuations give a unique term with smallest 3-adic order.
A sum of rational numbers with a unique smallest valuation cannot be
zero. A singleton class cannot cancel either. Hence all three roots
are rational. This reasoning also covers `Dg=0` and a guard with odd
valuation; it does not presume an integral auxiliary root.

It follows that `E Df=g2^2` and `Dg=g^2` for integers `g2,g`, since a
rational square root of an integer is integral. The crucial coprimality
identity is

    Df = 1+Delta U^2 E, so gcd(E,Df)=1.

Both factors are positive. Unique prime factorization therefore splits
the product square into

    E=tau^2, Df=f^2,

with positive integers `tau,f`. This implication is valid even if
`E=1`. Define the proof-only strong ordinate

    I = U tau.                                                (3)

Then `c^2|I`, `I!=0`, `|I|>=c^2`,
`f^2=1+Delta I^2`, and `Q=(Delta I)^2`.

In the rational chart the auxiliary `y=sqrt(Cy/delta)` is rational.
In the integral chart set `y=sqrt(delta Cy)/delta`; it is rational
and has the same square. In either case

    QV^2-(Q-1)y^2=1.                                         (4)

The adjacent-coefficient descent makes `y` integral. To record why,
write `|y|=a/b` in lowest terms. Equation (4) gives `b^2|(Q-1)`.
For `V>1,y>0`, the norm-preserving transformation

    V'=(2Q-1)V-2(Q-1)y, y'=(2Q-1)y-2QV

has integral first coordinate, preserves the reduced denominator `b`,
and satisfies `-V<V'<V`. The inequalities follow from
`V<y<QV/(Q-1)`; the norm excludes `V'=0`. Reflect signs as needed
and descend to `|V|=1`, where `|y|=1`. Thus `b=1`.

## 5. The scalar carrier and restoration of the source kernel

After root extraction, the rational factor is an integer identity

    S(n+V)-Ac = S(+-3tau f +-9g +-y).

For the integral chart replace `V,y` by `delta V,delta y`.
Consequently `S|Ac`, and in particular `H^5|Ac`.

Expand the homogeneous carrier:

    Phi_H(z)=(z^2+3H^2)(z^3-19H^3)
            =z^5+3H^2z^3-19H^3z^2-57H^5.

For a prime `p` with `p^e` exactly dividing `H`, suppose
`b=v_p(z)<e`. The leading term has order `5b`, and each other term
has strictly greater order, even when p divides 3, 19, or 57.
It follows that `H^5|Phi_H(z)` forces `H|z`, also for negative H.
Apply this to `z=HT+K`: we recover **H|K**.

Now set, solely for the source interface,

    r_old=r tau, T_old=tau T, I=s r_old c^2=U tau.

The strong and auxiliary expressions restore *exactly*:

    1+Delta I^2 = 1+Delta U^2 E = Df,
    (Delta I)^2 = Delta^2 U^2 E = Q,
    4I T_old = 4U tau^2 T = 4UET,
    V = f^2(c-R+4I T_old)-c.

The unrestricted signed source permits arbitrary nonzero integer strong
multipliers; no oddness assumption is imposed on `r_old`.
All the other signed front-end registers and both strict guards are
unchanged. Thus every hypothesis of the source interface in Section 2
is present, including `c^2|I` and the independently recovered `H|K`.

For clarity, the inherited argument first uses absolute Pell folding
with `B0=|a+2|`, `C0=|c|`, `I0=|I|`, and `|f|>2I0` to find an
index `p` with `C0=psi_B0(p)`. The condition `C0^2|I0`, together
with Lucas multiplication, supplies the strong-index divisibility even
for even multipliers. The auxiliary residues give `R=+-p (mod C0)`;
the strict first-index bounds then force `p=R`. The whole-product
argument combines `H|K` with the inherited size estimates to obtain
`sign(c)X=2^R`, restores a signed main root `d` with
`d^2=1+Delta c^2` and `H|(d-X-ac)`, and hence restores the native
kernel. These are the same pinned lemmas, used only after all their
hypotheses have been established. The named native/refutation theorem
therefore gives a finite syntactic ZFC refutation.

## 6. Completeness and its quantifier order

Start with a finite syntactic ZFC refutation, and take the canonical
native witness supplied by the retained calibration. In particular
`A0=a+2>1` is even, `R=3 (mod 4)`,
`c=psi_A0(R)>0`, `c=R (mod 4)`, and the first norm is
`E=tau^2` with `tau>0`. The strict guards hold. Choose the joint
positivity witness `t`, then a nonzero positive guard witness `s` with
`Dg=g^2`. If `Pair=1`, choose `s=1,g=0`; otherwise ordinary Pell
existence supplies them, exactly as in the parent.

Apply the **full-residue** interpolation theorem with

    N = s tau.

It returns a fixed strong pair `I,f`, before any residue request, with

    4s tau c^2 | I,

and every residue class modulo this same I attainable by an auxiliary
coordinate `T_old`. Define

    U=I/tau, r=I/(s tau c^2).

These are integers, `U=s r c^2`, and the new `Df,Q` equal the strong
ones. The canonical main projection supplies `H|K`; put `kappa=K/H`.
Intersectivity of
`pi(x)=(x^2+3)(x^3-19)` gives a residue `a_res` modulo U with

    pi(a_res+kappa)=0 (mod U).

Now request the attainable old auxiliary residue

    T_old = tau a_res (mod I).                               (5)

Since `I=tau U`, condition (5) ensures `tau|T_old`. Define
`T=T_old/tau`; dividing (5) gives exactly

    T = a_res (mod U).

The auxiliary equality is consequently the new equality
`V=f^2(c-R+4UET)-c`. Moreover

    Ac/S = pi(T+kappa)/U

is an integer. All three normalized roots are integral. Finally choose

    n=Ac/S+3tau f+9g+y-V

in the rational chart, or

    n=Ac/S+3tau f+9g+delta y-delta V

in the integral chart. These are unrestricted integers and make a
conjugate factor vanish.

The witness order is thus canonical front end, `t`, `s`, fixed `I,f`
with prescribed `s tau` divisibility, fixed `U,r`, an intersective
residue modulo U, an interpolated `T_old` modulo I, quotient `T`,
and finally n. No strong pair is changed after the residue request;
no coprimality between tau and U or between H and U is assumed.

For reference, intersectivity of the quintic follows from the standard
cubic discriminant argument. Away from 2,3,19, either `x^3-19` has a
simple root or its irreducible cubic Frobenius is a 3-cycle, so its
discriminant `-27*19^2` is a square and `x^2+3` has a simple root.
At 19 the quadratic root 4 is simple; at 2 the cubic root 1 is simple.
At 3 put `x=1+3u`: the equation reduces to
`u+3u^2+3u^3=2`, whose derivative is 1 modulo 3. Lifting and finite
CRT give roots modulo every positive integer. This is the classical
intersective quintic already used by the retained parent, not a new
claim of historical priority.

## 7. Exact degree 1084 and exact operation count

Degree means ordinary total degree in the twelve independent variables;
all six fixed coefficient ports have degree zero. The key degrees are

| Register | U | E | Delta | Df | delta | b | V | Cy | S | Ac |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Degree | 4 | 34 | 12 | 54 | 66 | 39 | 93 | 252 | 34 | 45 |

Write `z0=Sn-Ac`, of degree 45, and `omega=fs-fc`. In the rational
chart, the exact cancellation identity is

    omega=delta z0^2+2delta S V z0-S^2(V^2-1).

Its unique highest term is `-S0^2 V0^2`, of degree 254; the other
candidate degrees are 156, 238, and 68. Subscript zero denotes the
highest homogeneous part. The squared arguments have degrees

    deg(fa)=222, deg(fb)=180, deg(fc)=deg(fs)=320.

Rewrite the literal Pe without division:

    Pe=omega^2-2(fa+fb)(2fc+omega)+(fa-fb)^2.

Its unique top term is `-4fa0 fc0`, of degree 542. The complete list
of competing degree bounds is `508,476,500,434,444,402,360`.
The correction `64fs fc fa fb` has degree 1042, smaller than
`2*542=1084`. Thus the full leading form of P is `16fa0^2 fc0^2`.

To verify it is nonzero after specializing all fixed coefficients, put

    q0=6 beta j, X0=12q0 w, Y0=2q0^3 v,
    a0=X0Y0, U0=s r c^2,
    E0=h^2 X0^4 Y0^6,
    S0=2^10 a0^5 U0,
    delta0=a0^4 U0^2 E0,
    Df0=a0^2 U0^2 E0,
    V0=4a0^2 U0^3 E0^2 T.

Here the `4UET` term in b has degree 39 and uniquely dominates R,
of degree 5. Consequently every displayed leading form is a single
monomial. The **entire** degree-1084 homogeneous part is

    2^1144 * 3^760 * beta^624
        * j^624 w^132 v^164 h^32 s^32 r^32 c^64 T^4.           (6)

The exponent sum is 1084 and authentic beta is positive. This proves
exact degree rather than a syntactic estimate or line-test conjecture.

For the integral control the corresponding identity is

    omega=z0^2+2S delta V z0-S^2 delta V^2+S^2 delta.

Its top degree is 320, so `omega^2` uniquely dominates Pe and yields
degree 1280. The full highest homogeneous part is

    2^1320 * 3^880 * beta^728
        * j^728 w^152 v^192 h^40 s^40 r^40 c^80 T^8.

The literal operation census, independently recounted from all live
nodes, is 75 multiplications, 25 additions, 23 subtractions: **123**.
Loading a fixed integer or variable is not counted as arithmetic; every
binary multiplication by a scalar is counted. The final norm takes 13
operations, and the complete front end and carrier take 110. Every
node is live, so no unused arithmetic is hidden in the census. Register
abbreviations are not additional variables.

## 8. Reproducible finite checks and their boundary

Run with Python 3 and no third-party dependency:

    python3 -B build.py --check
    python3 -B verify.py --output CHECKS.json
    python3 -B -O verify.py --output CHECKS_OPTIMIZED.json

The independent verifier does not import the producer. It checks:

* every displayed register in free local polynomial rings, including
  the saturation and the indispensable factor E in the auxiliary term;
* all 35 coefficients of the full three-root norm, using the retained
  independent successive-conjugation oracle;
* the centered omega and Pe identities as universal polynomial
  identities, and the three exact restoration identities modulo
  `tau^2-E`;
* all live-node counts, variables, ports, topology, and exact leading
  monomials at every gate after the one separately proved cancellation;
* every retained file pin, complete six-coefficient payload, and the
  full source34 coefficient recipe and seed;
* rejection of corrupted auxiliary, strong, guard, carrier, and output
  expressions, both under ordinary and optimized Python.

These checks certify the polynomial, coefficient binding, counts, and
degree algebra. They do not mechanically verify the signed Pell and
interpolation arguments, which are ordinary proofs above using the
exact retained sources, independently read by a second agent. The
native/compiler/refutation calibration has not been replaced or newly
formalized. This distinction is part of the result.
