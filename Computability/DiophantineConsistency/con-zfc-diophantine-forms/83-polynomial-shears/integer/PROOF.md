# Double centering and a transport pivot for integer consistency equations

## 1. Precise result and comparison

This component supplies five ordinary polynomials with fixed integer
coefficients, each given as the sum of the squares of its listed residuals.
Every variable ranges over all of Z.

| Polynomial packet | Variables | Residuals | Exact total degree |
|---|---:|---:|---:|
| `centered23_degree10.json` | 23 | 11 | 10 |
| `pivot21_degree16.json` | 21 | 9 | 16 |
| `pivot20_degree20.json` | 20 | 8 | 20 |
| `pivot19_degree32.json` | 19 | 7 | 32 |
| `pivot18_degree88.json` | 18 | 6 | 88 |

For each polynomial P, composition with the stated source calibration gives
the ordinary theorem formalizable in ZFC:

    (exists x in Z^n, P(x)=0) iff (there is a finite ZFC refutation).

Thus ZFC proves `(P has no integer zero) iff Con(ZFC)`. This does not assert
that ZFC proves either side. It does not assume consistency to define any
coefficient. It does not claim a new kernel-checked theorem or an encoded
derivation in the repository's object-language ZFC calculus.

The inspected repository snapshot is
`c1a102936aca437e9999530a0111e6ddab56dc6d`. In addition to placed sources
31--75, the comparison includes all five archives then in `docs/incoming`.
In particular, the incoming Joint Guards package supplied 25/8, 23/12,
22/16, 21/20, 20/32, and 19/88, while Radical Guard Descent supplied 22/14.
The new forms improve the degree at 23 variables (12 to 10), at 21 variables
(20 to 16), at 20 variables (32 to 20), and at 19 variables (88 to 32).
The 18-variable degree-88 endpoint saves a further variable. The preexisting
22-variable degree-14 form remains a separate useful point. The older
ten-integer high-degree equation still has fewer variables. No single
scalar definition of "simplest" makes these different comparisons identical.

These are new combinations and projections relative to the inspected
packets. The constituent root translations and monic transport pivot have
explicit prior appearances in the incoming Budget and Centering and Round11
packages, respectively. No external priority or global optimum is claimed.

## 2. Exact fixed numerals and inherited boundary

Every new packet uses the same six fixed ports:

    beta = 2^1064921 - 1,
    K0, MC, MF = the whole source-34 mixed-parity-unrounded-1064921 tuple,
    cone_A = 2^1113,
    cone_B = 2^666104.

MF is the already shifted high mask; it must not be shifted again. The
actual minimal unsigned little-endian bytes, compressed with gzip, are
included in `coefficients/`. `BINDING.json` states their exact byte lengths
and SHA256 values. The bytes themselves, rather than their digests, specify
the fixed integers. Their combined uncompressed size is 615,883 bytes.
They are coefficient leaves, not existential variables.

The literal parent packets and their ordinary proofs are retained under
`upstream/`. `SOURCE_PINS.json` authenticates their exact bytes and the
incoming archive. The source chain is: the source-34 native/K215 calibrated
arithmetic interface; source-64 signed Pell recovery; source-70 residue
orientation; source-71 determinant guard; source-68 simultaneous positivity;
and the incoming Joint Guards compositions and projections. The new steps
below are elementary polynomial bijections on these already specified
integer zero sets. They introduce no further canonical-witness restriction.

The inherited source proofs assert ordinary arithmetic formalizability in
ZFC. Full compiler/global calibration and the final encoded object-language
biconditional are not supplied by this component. Exact finite algebra
checks do not close those separate formalization obligations.

## 3. A complete equation in 23 integers of degree ten

Use the 23 independent coordinates

    J,F,alpha,z,f,h,r,v,w,tau,eta,zeta,nu,gamma,o,j,E,a,I,t,p1,p2,p3.

The packet uses the names J3, v_scale, w3, pair_root and pair_pos1..3 for
J,v,w,t,p1..3. Define polynomial abbreviations, with no extra quantifiers:

    q = beta*(3J+1)+1,                 W = 4*(3w+1),
    X = qW,                            Y = a-E,
    k = eta+zeta,                      c = Yk+eta,
    V = fo-c,                          C = q-F-alpha,
    H = 4a+3,                          Delta = a^2+H,
    T = E(c-eta),                      S = X+gamma H,
    R = ((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)(3J+1),
    G = (cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    Z = eta zeta,                      Pos = 1+p1^2+p2^2+p3(p3+1).

The eleven residuals are:

    B1  = a-E-(2v+1)q^3,
    B2  = E-XY,
    B3  = tau^2+(2tau-k)T-1,
    B4  = 2acS+S^2-Hc^2-1,
    B5  = k-1-hE-R,
    B6  = (K0+W)C-F-z(q-1),
    B7  = I-(2r+1)c^2,
    B8  = I^2-Delta(f^2-1),
    B9  = (V+nu)^2-I^2 nu(2V+nu)-1,
    B10 = V+k-1-cj-hE,
    B11 = GZ-(t^2-G-Z+1)^2-Pos.

The single equation is `sum(Bi^2,i=1..11)=0`. All exponents are fixed
nonnegative integers. In particular there is no exponentiation relation,
unbounded list, implicit quantified register, or division in this equation.

### Exact zero-set equivalence

The incoming parent `joint25_octic.json` has independent c,V and y, and
uses `k0=1-V+jc+hE` in its first Pell norm and in its c equation. Its
penultimate row is `L=k-k0`. On the common zero set, replacing k0 by k
is justified by this retained row. More precisely, subtract `(a-E)L`
from the c row, subtract `T L` from the first norm after its root
translation, and add L to the packing row. These are invertible polynomial
row operations, since L remains a residual.

Now make the two triangular integral changes of coordinates

    tau_old = tau + E(c-eta),
    y_old   = V + nu,

and eliminate the monic definitions `c=(a-E)k+eta` and `V=fo-c`.
The cancellation identities are

    (tau+T)^2-T(k+T)-1 = tau^2+(2tau-k)T-1,
    (ac+S)^2-(a^2+H)c^2-1 = 2acS+S^2-Hc^2-1,
    I^2(V^2-(V+nu)^2)+(V+nu)^2-1
      = (V+nu)^2-I^2 nu(2V+nu)-1.

For complete row-by-row transparency, number the parent's residuals
0,...,12 in their literal order and the displayed new rows B1,...,B11.
After restoring c,V,tau_old,y_old, its rows are exactly

    B1, B2, (a-E)B10, B3+T B10, B4, B5-B10,
    B6, 0, B7, B8, B9, B10, B11.

Therefore any new zero gives an old zero. Conversely, an old zero supplies
the unique new tau=tau_old-E(c-eta), nu=y_old-V, and its c,V already equal
the displayed restorations; all eleven new rows vanish. These maps are
inverse bijections of the full integer zero sets. This step preserves the
private positivity witnesses as well as the arithmetic coordinates.

### Degree ten, exactly

The degrees of B1,...,B11 are

    4,3,4,5,4,2,5,4,5,3,4.

Thus their sum of squares has degree at most ten. Only B7 contains r.
Since c=(a-E)(eta+zeta)+eta, the coefficient of `r^2 a^4 eta^4` in
B7 squared is exactly 4. Every other squared residual has r-degree zero,
so the same coefficient in the complete polynomial is exactly 4. This
proves degree ten for the actual fixed numerals, not just for generic ports.

## 4. A transport pivot with a polynomial inverse

The parent systems all contain

    (K0+W)(q-F-alpha)-F-z(q-1)=0.

First replace alpha by the complement coordinate C via
`C=q-F-alpha`, or inversely `alpha=q-F-C`. This is an integral polynomial
coordinate automorphism. The transport row is then monic in F, so set

    F = (K0+W)C-z(q-1),
    alpha = q-(K0+W)C+z(q-1)-C.

Delete F and its transport row and substitute these expressions in every
other residual. The new system and the parent system have inverse integer
polynomial maps on their zero sets. No coprimality, sign, divisibility or
canonical-completeness argument is required for this projection.

The pivot was already used in incoming Round11 at a less compressed point.
Its useful new application here is to systems where higher-degree Pell or
joint-sign rows already determine the degree. The pivot raises the degree
of F to two, the packing row to five, and the determinant G to four;
these costs do not raise the dominant degrees in the selected four parents.

| Literal parent | New variables | New rows | New residual degrees |
|---|---:|---:|---|
| joint22_degree16 | 21 | 9 | 4,3,3,4,4,5,6,8,8 |
| joint21_degree20 | 20 | 8 | 6,6,4,10,5,10,10,8 |
| joint20_degree32 | 19 | 7 | 11,14,14,5,14,10,16 |
| joint19_degree88 | 18 | 6 | 34,14,5,14,10,44 |

The polynomial identity underlying the packing degree estimate is

    R=(q-F)(q^3-q)-C(q^2-1)+(MC+q MF)(3J+1).

The highest possible degree after F becomes quadratic is five. The
joint-sign residual is quadratic in its determinant argument G, so the
G contribution has degree at most eight. This explains why that pivot is
especially cheap after the degree-16 stage.

## 5. A compact complete equation in 18 integers

The 18 independent coordinates are

    J,C,z,f,h,r,v,w,tau,y,gamma,o,j,c,t,p1,p2,p3.

Set q,W,X as before; define these additional polynomial abbreviations:

    Y=(2v+1)q^3,       E=XY,                a=(X+1)Y,
    F=(K0+W)C-z(q-1),  alpha=q-F-C,        V=fo-c,
    k=1-V+jc+hE,      eta=c-Yk,            zeta=k-eta,
    H=4a+3,           Delta=a^2+H,         I=(2r+1)c^2,
    T=E(c-eta),       D=X+ac+gamma H,
    R=(q-F)(q^3-q)-C(q^2-1)+(MC+q MF)(3J+1),
    G=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
    Z=eta zeta,       Pos=1+p1^2+p2^2+p3(p3+1).

The six residuals are

    A1=tau^2-T(k+T)-1,
    A2=D^2-Delta c^2-1,
    A3=cj-V-R,
    A4=I^2-Delta(f^2-1),
    A5=I^2(V^2-y^2)+y^2-1,
    A6=GZ-(t^2-G-Z+1)^2-Pos.

The promised ordinary polynomial is `P18=sum(Ai^2,i=1..6)`. This compact
formula is completely inlined in its JSON packet, so the number 18 does
not conceal separate X,Y,E,a,F,alpha,V,k,eta,zeta,H,Delta,I,T,D,R,G,Z,Pos
coordinates. The packet is a direct polynomial projection of the literal
19-variable parent, not an asymptotic or conditional construction.

The 19-variable degree-32 sibling retains eta as an independent coordinate
and adds `c-eta-Yk=0`; the other five arithmetic rows and the same joint
guard use this independent eta. It has seven residuals. This keeps Z at
degree eight instead of twenty-two, which is why one extra variable lowers
the total degree from 88 to 32.

## 6. Exact degree certificates for the four pivot forms

For the 21-variable form, the reduced auxiliary residual has leading term
`a^2 f^4 o^2`, with coefficient 1. Its square contributes
`a^4 f^8 o^4` with coefficient 1. The new guard's degree-eight leading
part depends only on the leading degree-two F, hence contains no f or o.
No other residual contributes to this monomial. The exact degree is 16.

For the 20-variable form, the strong Pell residual contains the degree-ten
term `-Y_top^2 f^2`, where

    Y_top=54 beta^3 J^3 v.

Its square has coefficient `54^4 beta^12=2^4 3^12 beta^12` at
`f^4 v^4 J^12`. The main norm has no f and the auxiliary norm has no J;
the new guard has degree at most eight. The exact degree is 20.

For the last two forms,

    X_top=36 beta J w,
    Y_top=54 beta^3 J^3 v,
    E_top=1944 beta^4 J^4 w v.

In the 19-variable form, `k_top=h E_top` has degree seven and
`Z_top=eta h E_top` has degree eight. The determinant has degree four,
so the only degree-sixteen homogeneous part of a residual is `-Z_top^2`.
The SOS coefficient at `eta^4 h^4 w^4 v^4 J^16` is therefore

    1944^4 beta^16 = 2^12 3^20 beta^16 > 0.

Its degree is exactly 32.

In the 18-variable form, `eta=c-Yk` has degree eleven, with

    eta_top=-104976 beta^7 h J^7 w v^2
           =-2^4 3^8 beta^7 h J^7 w v^2.

Then `Z_top=-eta_top^2` has degree twenty-two. The joint-sign row has
degree forty-four with top part `-eta_top^4`. All other residuals have
degree at most thirty-four. Thus the coefficient at `h^8 w^8 v^16 J^56`
in the complete SOS is

    2^32 3^64 beta^56 > 0.

The degree is exactly 88. All four certificates remain nonzero after
specializing beta to the actual Mersenne integer. These are exact
degree statements, not uncancelled circuit upper bounds.

## 7. Reproduction and verification scope

With Python 3 and SymPy 1.14 installed, run

    python3 build.py
    python3 check.py

`build.py` emits all five complete packets. It checks declaration closure,
every variable's occurrence, the exact degree and a positive coefficient
at that degree. Its weighted-degree computation assigns weight zero to
the six fixed coefficient leaves.

`check.py` imports no builder. It authenticates every supplied actual
numeral, verifies the complete thirteen-row centering restoration,
independently checks the monic transport identities and all retained
literal substitution identities, and checks degree bounds and selected
degree certificates. Its additional signed modular evaluations use the
actual coefficient integers and two moduli; these are transcription
diagnostics, not proofs of the unbounded arithmetic theorem. Neither
checker uses removable Python assertions for acceptance.

`BUILD_CHECKS.json` and `INDEPENDENT_CHECKS.json` record successful runs.
The retained source proofs identify the inherited universal assumptions.
There is no claim that finite random evaluation establishes polynomial
identity or the ZFC consistency equivalence.

## 8. Further research questions

1. The transport pivot removes a coordinate without changing degree once
   the existing maximum residual degree is at least eight. Which other
   source rows admit a monic pivot after an integral coordinate change?
   Any candidate must preserve integer integrality rather than silently
   solving by division.
2. Can the 19-variable degree-32 form be reduced to degree below 32 without
   restoring an eliminated coordinate? Its largest degree comes only from
   squaring the simultaneous positivity guard; the arithmetic rows have
   degree at most fourteen.
3. Can a different existential positivity certificate avoid the second
   squaring of the degree-eight sign expression while retaining four or
   fewer private integer variables? This would improve the 19-variable
   equation even before changing the underlying compiler.
4. The 18-variable equation incurs degree 88 because eliminating eta
   produces a degree-eleven polynomial in a sign guard. Can a new
   orientation lemma avoid that substitution cost, while still excluding
   every noncanonical integer solution?
5. A small algebraic compiler independent of the K215/native pipeline
   could improve coefficient height and proof complexity more than these
   projection steps. Measuring description size, coefficient bytes and
   verification dependencies should accompany any variable-count claim.

