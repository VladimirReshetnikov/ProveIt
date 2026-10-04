# An explicit degree-12 Diophantine certificate for five-signal infinite validity

4 October 2026. This is a new arithmetic construction for the specific independently audited five-live-signal complete-macro predicate. It does not modify that machine, replay a trajectory, run an upstream program, or replace the geometric proof by experimental evidence.

## 1. Result and scope

For the fixed five-signal machine in `sources/five-signal-PROOF.md`, let `Valid(g1,g2,g3)` mean that its specified complete macro can be iterated indefinitely from the outgoing section with positive integer gaps `(g1,g2,g3)`. Its real/rational/integer finite-polynomial-sign obstruction was independently proved in the supplied geometry packet.

**Native-input theorem.** The explicit integer polynomial represented by `evidence/three-input-linear.dag.json` has three ordinary positive integer inputs, **81 ordinary positive integer witness variables**, and **exact total degree 12**. For every positive integer gap triple,

    Valid(g1,g2,g3)  iff  there exist w1,...,w81 > 0 with F(g1,g2,g3,w)=0.

Its literal arithmetic source has **344 binary gates: 136 multiplications, 110 additions, and 98 subtractions**. Thus it has 136 M + 208 A when additions and subtractions are combined. Fixed integer coefficients are free leaves; multiplying by them is charged. There are 44 named equations and exactly two completely expanded POWER modules.

**One-input theorem.** Let `pair(a,b)=(a+b)(a+b+1)/2+b` for naturals a,b, and encode positive gaps by

    code(g1,g2,g3) = 1 + pair(g1−1, pair(g2−1,g3−1)).

This is a bijection from positive integer triples to positive integers. The separately emitted `evidence/one-input-linear.dag.json` defines the transported predicate on its **one ordinary positive integer input** using **85 positive witnesses, 46 equations, and 367 gates = 144 M + 223 A**, again with exact degree 12. Its decoding arithmetic is included. The native theorem and one-input theorem have different input counts and ledgers.

The proof uses the supplied geometric validity theorem and the explicit constructive Pell theorems underlying the displayed POWER equations. It does **not** use a generic MRDP representation as the final representation, an unexpanded exponentiation oracle, a comparison oracle, selector branches, a variable-length conjunction, or a hidden array. All quantifiers in the final formulas range over ordinary positive integers. There is no real-witness equivalence or finite-fold/singlefold/unique-witness claim. In fact, the positive-pair representation of each signed witness visibly gives infinitely many witnesses whenever one exists.

## 2. The inherited geometric predicate, in integer coordinates

Write

    D = g1+g2+g3,   x = g1,   y = g1+g2,
    A = 3x−D,      B = 3y−2D,
    delta = 4D²−205(A²+B²),
    U = 6A−13B,    V = 13A+6B.

The centered normalized position is `(A/(3D), B/(3D))`. The unique tangency point is `p=(4/205,−26/615)` and the critical squared radius is `4/1845`. Consequently delta has exactly the sign of the radius deficit. Exact division by `p=(2/615)(6−13i)` gives

    eta = ((A+iB)/(3D))/p = (U+iV)/(2D).

Also `U²+V²=205(A²+B²)`. In particular eta has modulus one on delta=0. The independently audited physical theorem is

    Valid iff delta>0, or delta=0 and eta is not ((3−4i)/5)^m for any m>=0.

Negative delta is invalid. This is a criterion for the actual complete collision word, including strict exclusion of the omitted triple contact, not merely a statement about a matrix orbit. Reusing this theorem does not repeat or extend the physical audit.

## 3. The complete outer certificate

All values named here are aliases for expressions or the declared integer variables; there are no uncharged defining relations. The emitter expands every alias into the recorded arithmetic DAG.

Use natural variables `delta,n,k,L_C,H_C,L_S,H_S`, positive variables `h,q,r,s,t,J`, and signed integer variables `u,v,a1,a2,a3,C,S,kappa`. Instantiate the two fully displayed POWER modules from Section 7 to define

    P = POWER(5,n),   b = 4P+1,   T = POWER(3+4b,n).

The fourteen outer equations are:

1. `4D² = 205(A²+B²)+delta`
2. `U = h u`
3. `V = h v`
4. `2D = h q`
5. `a1 u+a2 v+a3 q = 1`
6. `q = P r`
7. `r = 5k+s`
8. `s+t = 5`
9. `C+P = L_C`
10. `P−C = H_C`
11. `S+P = L_S`
12. `P−S = H_S`
13. `T−C−bS = kappa(b²+1)`
14. `delta²+(r−1)²+(u−C)²+(v+S)² = J`

The last right-hand side is **positive**, not natural: it enforces the strict nonzero condition. The radius slack is **natural**, so equality at the critical circle is permitted. Bounds 9–12 are closed bounds, also with natural slacks. Positivity of both s and t is essential.

Every natural z is replaced by one positive leaf `z.Plus` minus 1. Every signed z is replaced by `z.Positive−z.Negative`, where both leaves are positive. This equals `(z.Positive−1)−(z.Negative−1)` and represents every integer. It uses one subtraction gate, with no unnecessary intermediate shifts. Positive quantities are single positive leaves. All these domain operations are present and charged in the DAG.

The 29 outer leaves are seven natural leaves, six positive leaves, and sixteen leaves for the eight signed quantities. The POWER outputs P and T are included in their respective 26-leaf modules, not counted again. Hence `29+2*26=81`.

## 4. Exact denominator and exponent, including zeros

Equations 2–5 imply `gcd(u,v,q)=1`: every common divisor divides 1. Conversely every primitive integer triple has signed Bezout coefficients a1,a2,a3. Because h>0, these equations force

    h = gcd(U,V,2D),  u=U/h,  v=V/h,  q=2D/h.

The gcd is positive, even when U or V vanishes, since 2D>0. If U=V=0, the equations force u=v=0 and q=1; h=2D and a3=1 supply witnesses. There is no zero-component exception.

The integer q is exactly the least common positive denominator of `u/q` and `v/q`. Indeed, any integer d which clears both fractions has q dividing du and dv; multiplying the Bezout equation by d gives q dividing d. This argument avoids separately reducing two fractions and proves the joint denominator directly.

POWER gives P=5^n. Equations 7–8 give `s in {1,2,3,4}` and `r=5k+s`, so r is positive and not divisible by 5. Equation 6 then forces n to be the canonical 5-adic valuation of q, and r its remaining factor. Conversely these values always exist for every positive q. This construction is used on interior points too; it needs no boundary selector.

## 5. Bounded extraction of a complex power using two ordinary powers

Let `C_n+iS_n=(3+4i)^n`. Its modulus is P=5^n, so `|C_n|,|S_n|<=P`. Evaluating the binomial identity at `i -> b` modulo `b²+1` yields

    (3+4b)^n = C_n+bS_n mod (b²+1).

Thus the true pair has a signed quotient kappa satisfying equation 13 and the four bounds. Conversely, if C,S also satisfy them, put dC=C−C_n and dS=S−S_n. Then `b²+1` divides `dC+b*dS`, while

    |dC+b*dS| <= 2P(1+b) = 8P²+4P
                            < 16P²+8P+2 = b²+1.

The integer is therefore zero. Since `|dC|<=2P<b`, the equality `dC=−b*dS` forces dS=0 and then dC=0. This proves exact bounded extraction, without any restriction on the size or sign of kappa.

At n=0 this gives `P=1,b=5,T=1,C=1,S=0`. Thus exponent zero is covered by both the extraction proof and, independently, the POWER construction's positive-exponent shift below.

## 6. Why the final condition is exactly validity

For m>=1, reduction modulo 5 gives

    (3−4i)^m = 3+i mod 5,

because `3−4i=3+i mod 5` and `(3+i)²=3+i mod 5` in the quadratic quotient ring. Neither numerator coordinate is divisible by 5. Hence the joint denominator of `((3−4i)/5)^m` is exactly 5^m. The m=0 point is 1 with denominator 1.

If eta is a forbidden point, its reduced denominator therefore forces m=n and r=1. Its reduced numerator is exactly `(u,v)=(C,−S)`. Conversely r=1 and this numerator equality imply that eta is the forbidden inverse power. The orientation is deliberately `v+S`, not `v−S`. The forward point `(3+4i)/5` has `(u,v)=(3,4)` and `v+S=8`, so is accepted on the boundary.

**Soundness.** A positive-integer zero of the final sum-of-squares polynomial makes all 44 residuals zero. Equation 1 supplies delta>=0. The two exact POWER modules, gcd/valuation clauses, and bounded extraction determine all arithmetic quantities described above. Equation 14 says that either delta is positive or the boundary point is not a forbidden inverse power. The geometric theorem then gives infinite complete-macro validity.

**Completeness.** Suppose the positive-gap input is valid. Its radius deficit is a natural delta. Choose the positive gcd and primitive quotient, then signed Bezout coefficients. Choose the canonical n,r,k,s,t, and obtain witnesses for the two POWER modules. Set C,S to the actual complex-power coefficients, choose their four natural bound slacks and the integral signed kappa. If delta>0 the left side of equation 14 is positive. If delta=0, validity says eta is not forbidden, so one of the other three squared terms is positive. In either case use that positive integer as J. Convert each natural and signed quantity to positive leaves. Every equation holds and the polynomial is zero.

All these arguments are finite mathematical proofs. Neither density nor an unbounded orbit search is used to decide the arithmetic certificate.

## 7. POWER completely expanded, with its precise dependency

For any integer base B0>=2 and natural exponent e, introduce positive

    out,w,M,g,x,y,u,v,s,t,qb,qv,Jp,

two positive leaves whose values plus one give `a,beta>=2`, and natural

    dwb,dwk,dyk,alpha1,alpha2,sigma1,sigma2,tau1,tau2,rho1,rho2.

Set `k0=e+1` and `m0=B0*out` as arithmetic expressions. The fifteen equations are:

1. `x² = 1+(a²−1)y²`
2. `u² = 1+(a²−1)v²`
3. `s² = 1+(beta²−1)t²`
4. `beta = 1+4y qb`
5. `beta+u alpha1 = a+u alpha2`
6. `v = y² qv`
7. `s+u sigma1 = x+u sigma2`
8. `t+4y tau1 = k0+4y tau2`
9. `y = k0+dyk`
10. `w = B0+dwb`
11. `w = k0+dwk`
12. `M = m0+Jp`
13. `a² = 1+((w+1)²−1)(w g)²`
14. `2aB0 = M+(B0²+1)`
15. `x+M rho1 = y(a−B0)+m0+M rho2`

There are 13 directly positive leaves, two shifted-positive leaves, and eleven natural-adapter leaves: **26 positive leaves, 15 residuals**. The four pairs alpha, sigma, tau, rho give two-sided congruence quotients; none is dropped. In this literal source, one module uses **70 body gates: 31 M, 24 +, 15 −**, before the global residual-square assembly. This is a source-specific statement about the present expression sharing, not a claimed minimal circuit.

These are the independently audited prior POWER equations, reproduced explicitly rather than called as an opaque external module. Their number-theoretic dependency is the constructive theorem `Pell.matiyasevic` together with `Pell.eq_pow_of_pell` in mathlib4, commit `ac77769fabe23cb237559e7f56578dbead91499f`, file `Mathlib/NumberTheory/PellMatiyasevic.lean`, SHA-256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`. Its exact source is included inertly; no Lean build was run in this work.

For clarity, here is how the stated dependency specializes. Equations 1–9 are the nonzero-index branch of `matiyasevic`, since k0>=1 and y>=k0. They force x,y to be the Pell pair at index k0 for parameter a. Equations 10–15 are the positive-base, positive-index branch of `eq_pow_of_pell`, with its strict modulus bound. Equation 13 and w>=B0>=2 imply a>w>=B0, so the integer difference a−B0 agrees with the theorem's natural subtraction. The theorem gives `B0^k0=m0=B0*out`; cancellation of positive B0 gives `out=B0^e`.

Conversely the constructive Pell theorem supplies the auxiliary values for `B0^k0`. The auxiliary g cannot be zero, since that would make a=1. The Pell x,u,s are positive. y>=k0 is positive, v is explicitly positive, and hence qv=v/y² is positive. The congruence and beta>1 imply qb=(beta−1)/(4y)>0. The congruence `t=k0 mod 4y`, with `1<=k0<=y<4y`, excludes t=0. M>m0 gives the positive Jp. Signed congruence differences have two natural quotient witnesses. Thus the positive-domain specialization loses no solutions. This explains the paid domains as well as the exponent-zero shift; it does not appeal to generic Diophantine representability.

The first outer base is 5. The second is `3+4(4P+1)=16P+7>=23`, since POWER's output P is positive. Both exponents are the same natural n, so every POWER use satisfies its hypotheses before its semantics is applied.

## 8. Paid one-input decoding

For an external positive code z, introduce positive witness gaps g1,g2,g3 and a natural inner code j. Put a=g1−1, b=g2−1, c=g3−1 and impose the two integer equations

    2j = (b+c)(b+c+1)+2c,
    2(z−1) = (a+j)(a+j+1)+2j.

They uniquely decode the Cantor bijection stated in Section 1. For completeness, for any natural N there is a unique diagonal d with `d(d+1)/2<=N<(d+1)(d+2)/2`; the offset N−d(d+1)/2 is in [0,d] and gives the second coordinate, while d minus that offset gives the first. Apply this twice. Thus every positive code has exactly one decoded positive gap triple, without an input-validity promise.

The four new positive leaves and the two equations are explicit. Before adding their residuals they contribute 17 body gates: 6 M, 6 +, 5 −. The two new squared residuals and their additions to the sum cost a further 6 gates. The total increase is **4 witnesses, 2 equations, 8 M + 8 + + 7 − = 23 gates**. The degree of each decoding residual is two, so the final polynomial still has exact degree 12.

## 9. Literal source ledger and exact degree

The native linear-residue source has the following region ledger. Aliases name existing expressions and do not grant free arithmetic.

| Region | Positive leaves | Equations | M | + | − | Gates |
|---|---:|---:|---:|---:|---:|---:|
| Radius and U,V arithmetic | 1 | 1 | 12 | 6 | 4 | 22 |
| Primitive Gaussian fraction | 12 | 4 | 7 | 2 | 5 | 14 |
| Natural valuation exponent | 1 | 0 | 0 | 0 | 1 | 1 |
| POWER(5,n) | 26 | 15 | 31 | 24 | 15 | 70 |
| Valuation and positive residue | 4 | 3 | 2 | 2 | 1 | 5 |
| Extraction bases | 0 | 0 | 2 | 2 | 0 | 4 |
| POWER(3+4b,n) | 26 | 15 | 31 | 24 | 15 | 70 |
| Bounded complex extraction | 10 | 5 | 3 | 3 | 11 | 17 |
| Strict acceptance | 1 | 1 | 4 | 4 | 2 | 10 |
| Residuals, squares, and sum | 0 | 0 | 44 | 43 | 44 | 131 |
| **Total** | **81** | **44** | **136** | **110** | **98** | **344** |

All gates, inputs, and witness leaves are live in the output. The final polynomial is literally the sum of the squares of all named equation residuals, so zero is equivalent to their conjunction over integers. The source has only binary `+`, `−`, `*` operations and integer coefficients. All emitter loops range over fixed lists (the two modules, their fifteen equations, fixed witness lists, and fixed emitted residuals), never over an input or witness value.

Every outer residual has degree at most three (at most four in the optional quartic variant); the POWER residuals have degree at most six. Both POWER residual 13 polynomials have leading term `−w^4*g^2`. Squaring contributes `w^8*g^4` of degree twelve. The degree-twelve part of the total is a sum of squares of nonzero real homogeneous polynomials and cannot vanish identically. Hence the degree is **exactly twelve**, not just an upper bound. Degree is measured jointly in inputs and independent positive witness leaves.

The optional quartic version replaces s+t=5 by `(s−1)(s−2)(s−3)(s−4)=0` and drops the positive t leaf. It has one fewer witness but six more gates: +3 M, −1 addition, +4 subtractions. The equation count and exact degree are unchanged. Its separately emitted ledgers are:

| Source | Inputs | Positive witnesses | Equations | M | + | − | Gates |
|---|---:|---:|---:|---:|---:|---:|---:|
| Three-input linear | 3 | 81 | 44 | 136 | 110 | 98 | 344 |
| One-input linear | 1 | 85 | 46 | 144 | 118 | 105 | 367 |
| Three-input quartic | 3 | 80 | 44 | 139 | 109 | 102 | 350 |
| One-input quartic | 1 | 84 | 46 | 147 | 117 | 109 | 373 |

No minimality claim is made. The linear version is the primary certificate because its range proof and arithmetic are simpler.

## 10. Source pins and verification limits

The authoritative primary DAG hashes are:

- Three-input linear: `707721d1a8dca21b29acda57df8df6e763a1df89761f513122bec5edd9261ccc`
- One-input linear: `b64a268cc03033c13c020abc0cb12c1c81f9ba630aa75812ac84b08e2971efc3`

`sources/SOURCE_PINS.json` identifies every copied dependency and its byte hash. `evidence/*.receipt.json` gives source-specific gates, witness counts, equation counts, degrees, and liveness. `review/ALGEBRA_REVIEW.md` is a separately written review of the outer iff and edge cases. The fresh inert-DAG source audit and its exact sparse-polynomial receipts are in `independent_audit/`. `check_semantics.py` is newly written standard-library exact arithmetic; it imports neither the emitter nor any previous code.

The finite tests compare the outer constraints with independently calculated rational geometry on a positive-gap box, both orbit orientations through exponent 60, general rational critical-circle points, and nonprimitive gap scalings. They exhaustively test bounded extraction through P=125, check paid Cantor round trips, and give explicit counterexamples demonstrating the need for bounds, the primitive gcd condition, and the exact 5-adic valuation. They also construct and evaluate complete positive Pell witnesses for exponent zero in all four sources, both at the center and at a valid boundary point. Single-leaf perturbations are checked; freely varying Bezout coefficients multiplying zero are correctly recognized as neutral, not misreported as failures.

General nonzero-exponent Pell witnesses can be enormous; those auxiliaries are not numerically instantiated by the tests. Nonzero-power tests use independently computed ordinary integer power outputs, while the constructive Pell theorem supplies the all-exponent module equivalence. The finite tests are support, not a proof substitute. No upstream or saved program, author checker, physical simulator, or trajectory replay was executed. The inherited nonsemialgebraicity result and this positive-integer existential certificate are fully compatible.
