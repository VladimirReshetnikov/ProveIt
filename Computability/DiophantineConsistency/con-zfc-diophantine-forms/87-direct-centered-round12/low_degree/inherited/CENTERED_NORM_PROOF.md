# Composing signed bootstrap, calibrated cones, and joint positivity

## 1. Results and their precise scope

Five explicit equations improve the inspected repository's integer low-degree
frontier. The comparison snapshot is ProveIt commit
`2605669a532342f153b13eb6b4a0af4b54f5fa37`.

| Equation | Unrestricted integer unknowns | Residuals | Exact degree | Binary arithmetic gates |
|---|---:|---:|---:|---:|
| `sextic31.json` | 31 | 18 | 6 | 144 |
| `octic26.json` | 26 | 14 | 8 | 131 |
| `degree10_24.json` | 24 | 12 | 10 | 135 |
| `degree12_23.json` | 23 | 11 | 12 | 122 |
| `degree14_22.json` | 22 | 10 | 14 | 123 |

Every equation is the sum of the squares of its listed residuals. The retained
`degree12_25.json` is an intermediate, dominated by the 23-variable equation;
it records the exact elimination chain and is not another frontier claim.

The inspected wave-10 catalogue has 32-integer sextics and 27-integer octics
(sources 69 and 71), and a 26-integer degree-16 equation (source 68). The first
two rows save one variable at the same degree. Each of the final three rows
improves both coordinates of the degree-16/26-variable comparison. None improves the
high-degree ten-integer bound. The operation counts describe the supplied
straight-line evaluators, not optimal arithmetic circuits or bit complexity.

The contribution combines three mechanisms already present in sources 68, 71,
and 75 with further exact coordinate elimination, a nonzero-scale main-norm
replacement, and an auxiliary root shear combined with a strong-norm row
operation. These final two steps yield the degree-ten and degree-fourteen
endpoints; neither is simply a monic projection. No
priority over external mathematics or globally simplest equation is claimed.
The underlying K215/native-compiler/Pell calibration remains an explicitly
inherited ordinary mathematical theorem; no new end-to-end Lean/Rocq
certificate or object-language ZFC derivation is supplied.

## 2. The 23-variable equation, completely displayed

The nineteen arithmetic unknowns are

    J,F,alpha,f,h,r,v,tau,eta,y,gamma,o,j,E,c,a,I,u,Z.

The four additional guard unknowns are `t,p1,p2,p3`. All 23 range over all
integers. In the machine-readable files the names are respectively `v_scale`,
`pair_root`, and `pair_pos1,pair_pos2,pair_pos3`. This is only a renaming.

Use the complete source34 tuple `mixed-parity-unrounded-1064921`:

    beta = 2^1064921 - 1,
    K0, MC, MF = the authentic fixed native ports,
    A = 2^1113, B = 2^666104.

Here MF is already shifted by beta. All six fixed integers are supplied as
actual compressed minimal unsigned little-endian bytes in `coefficients/`,
with raw SHA-256 identities in `coefficients/BINDING.json`. No unspecified
choice of a proof-search program, exponent, or coefficient is left in the
equation. A and B are `cone_A` and `cone_B` in the JSON files; they are not the
source's main Pell parameter or root.

Define the following polynomial abbreviations, which add no unknowns:

    q = beta*J+1,
    C = q-F-alpha,
    H = 4a+3,
    Delta = a^2+H,
    X = 4q u^2,
    D = X+ac+gamma H,
    V = fo-c,
    k = 1-V+jc+hE,
    zeta = k-eta,
    R = ((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    G = (AF)(BC)-(q-AF-BC)^2,
    p = 1+p1^2+p2^2+p3(p3+1).

The eleven residuals are

    r1  = a-E-(2v+1)q^3,
    r2  = E-X(a-E),
    r3  = c-eta-(a-E)k,
    r4  = tau^2+(2tau-k)E(c-eta)-1,
    r5  = D^2-Delta c^2-1,
    r6  = k-R-1-hE,
    r7  = (K0 q+X)C-qF-Z(q-1),
    r8  = I-(2r+1)c^2,
    r9  = I^2-Delta(f^2-1),
    r10 = I^2 V^2-(I^2-1)y^2-1,
    r11 = G eta zeta-(t^2-G-eta zeta+1)^2-p.

The requested single polynomial is exactly

    P23 = r1^2+r2^2+...+r11^2.

Its degree is twelve. The expression is an ordinary integer polynomial:
every exponent involving an unknown is a displayed fixed nonnegative integer,
and the powers of two defining beta,A,B are fixed integer coefficients.

## 3. Why the final guard is exact

Let `Pos(x,y,z)=1+x^2+y^2+z(z+1)`. It is positive at every integer input.
It represents every positive integer n: apply the three-square theorem to
`4n-3`, whose residues exclude the three-square obstruction. Modulo four,
one of the squares is odd and the other two are even; write the three roots
as `2z+1,2x,2y` and divide the resulting identity by four.

For arbitrary integers x,y define

    Pair(x,y,t)=xy-(t^2-x-y+1)^2.

The elementary lemma of source68 is

    x>0 and y>0  iff  there exists t in Z with Pair(x,y,t)>0.      (1)

For soundness, a positive Pair forces xy>0. If x=-a,y=-b with a,b>=1,
the square subtracted is `(t^2+a+b+1)^2>ab=xy`, a contradiction.
For completeness put N=x+y-1>=1. Then `N<=xy` because
`xy-N=(x-1)(y-1)>=0`. Let m=floor(sqrt(N)). Choose t=m if
`N-m^2<=m`, and t=m+1 otherwise. In either case the square error is
strictly less than N: if N is a square it is zero; otherwise
`|t^2-N|<=m` and `m^2<N`. Thus Pair>0. No floor or square-root
operation appears in the final equation; they only select a witness in
this proof.

Consequently the final row of P23 is equivalent to `G>0` and
`eta*zeta>0`, with four existential guard coordinates. Two independent
Pos representations would require six. This equivalence is universal;
it does not assume a canonical input or the sign of q.

## 4. Why the calibrated determinant supplies the native signs

This is source71's guard, used with exactly its coherent native tuple.
For arbitrary real values of F,C,q put `U=AF`, `W=BC`. If

    U W-(q-U-W)^2>0,

then U,W have the same nonzero sign and

    |q-U-W| < sqrt(UW) <= (|U|+|W|)/2.

Thus q has their common sign and

    |q| > (A|F|+B|C|)/2 >= |F|+|C|,

since A,B>=2. It follows that `alpha=q-F-C` has that sign too. In
particular `F*alpha>0` and `F*C>0`. Each product has a Pos representation,
so any new zero restores the two old sign guards in source75. This
soundness argument is valid even before the Pell analysis has established
q>0.

Completeness uses canonical native witnesses, not every arbitrary old zero.
Source71 proves for those witnesses, with its actual fixed leading-digit
scales A,B,

    q/2 <= AF < 4q/5,
    q/2 <= BC < 3q/5,
    q>0.                                                       (2)

These estimates survive the source75 signed-bootstrap replacement: its
canonical modification changes only the scale/root witness u and the
cleared transport quotient Z, leaving q,F,C and the native tableau intact.
For completeness of (2), the full native digit and carry proof is retained
in `upstream/DETERMINANT_GUARD.md`; its constants are checked against the
actual bundled bytes. It uses the native block length 8801, radix 2^121,
top C position 3296, top F position 8791, and the literal leading clause
coefficient `105534389824824194647382298625`. The two scale exponent
identities are `121*8791+1113=1064921-97` and
`121*3296+666104=1064921-1`. No different coefficient tuple is spliced in.

Write `s=q/2`, `AF=s+x`, `BC=s+y`. Then
`0<=x<3s/5`, `0<=y<s/5`, and

    G=s^2+s(x+y)-(x^2+y^2+xy)>12s^2/25>0.

So canonical old zeros supply a positive determinant G and hence its Pos
representation. This proves both directions of the guard replacement at
the level of existence. It is deliberately not a bijection on arbitrary
old assignments of the native coordinates.

## 5. The signed source and the 31-variable sextic

Source75's `signed40_sextic.json` is obtained from source64's Q41 by
replacing its global-square/scale pair with

    X=4q u^2,
    (K0 q+X)C-qF-Z(q-1)=0.

Its proof, retained as `upstream/SIGNED_BOOTSTRAP.md`, allows both initial
signs of X. It uses the main, first, strong, and auxiliary Pell equations
to recover the odd rank R and then X=2^R and q>0. The cleared transport
implies q|Z, restoring the old transport quotient. Canonical completeness
sets `u=2^((R-t-2)/2)` when `q=2^t`, and Z=q times the old quotient.
The parity and gap needed for this recipe are inherited native properties.
That genuine existential reduction is not replaced here by a numerical test.

An integral root shear

    tau_old = tau_new+P-eta-zeta

and six monic substitutions produce the source75 34-variable sextic:

    P=eta+zeta+E(c-eta), F2=f^2, g=y^2-V^2,
    N=q(L+1), C2=c^2, X=D-ac-gamma(4a+3).

The centered first norm becomes exactly

    tau_new^2+(2tau_new-eta-zeta)E(c-eta)-1.

Every residual now has degree at most three. Replacing its two native
product guards by the determinant guard of Section 4 removes six private
unknowns and inserts three. The result has 31 unknowns and 18 residuals.
The row `I-(2r+1)c^2` is the only one involving r. Its square therefore
has coefficient 4 at `r^2 c^4`, proving exact degree six independently of
all fixed coefficients.

For a compact complete presentation of this sextic, retain the same names
q,C,H,X,R as above, but now set

    q=beta J+1, C=q-F-alpha, H=4a+3,
    k=eta+zeta, X=D-ac-gamma H,
    R=((q-1)(q-F)+alpha)L+(MC+q MF)J.

L,Delta,Baux,D,V,zeta are retained unknowns here. The eighteen rows are

    L-q^2+1,
    a-E-(2v+1)q(L+1),
    E-X(a-E),
    c-eta-(a-E)k,
    tau^2+(2tau-k)E(c-eta)-1,
    Delta-a^2-H,
    D^2-Delta c^2-1,
    k-R-1-hE,
    (K0 q+X)C-qF-Z(q-1),
    V+c-fo,
    k+V-cj-hE-1,
    I-(2r+1)c^2,
    Baux-I^2,
    Baux-Delta(f^2-1),
    Baux(V^2-y^2)+y^2-1,
    X-4q u^2,
    G-Pos(cone1,cone2,cone3),
    eta*zeta-Pos(ez1,ez2,ez3).

As always the single equation is the sum of their squares.

## 6. The 26-variable octic

Starting with the preceding sextic, eliminate the monically defined
coordinates

    L=q^2-1, Delta=a^2+4a+3, Baux=I^2.

Their three definition rows vanish identically. All remaining rows have
degree at most four. Replace the last two Pos rows by

    Pair(G,eta*zeta,t)=Pos(p1,p2,p3).

Here zeta is still a retained coordinate, so both positive quantities G
and eta*zeta are quadratic. The new row is quartic. The result has
`31-3-6+4=26` unknowns and `18-3-2+1=14` residuals. It is an octic.
Its coefficient of the private monomial t^8 is exactly 1: t occurs only
in the new guard, whose t^4 coefficient is -1. This certificate is again
independent of all coefficient specialization.

The two residual representations are related by the exact positivity
lemma, and the three coordinate eliminations by integral polynomial
maps inverse to projection. Thus integer solvability is preserved.

## 7. Why only 23 unknowns are needed at degree twelve

The 26-variable octic still contains three monically defined coordinates:

    zeta=1-V+jc+hE-eta,
    D=4q u^2+ac+gamma(4a+3),
    V=fo-c.

Eliminate them in that order. The first deletion raises eta*zeta to
degree three and the merged guard to degree six. That alone permits a
25-variable degree-twelve equation, but stopping there wastes the newly
available degree budget. The second deletion raises the main norm to
degree six. The third raises the auxiliary norm to degree six. Neither
exceeds the degree already required by the merged positivity row.

The three deleted defining rows are exactly monic in the deleted
coordinates; after their substitution each is identically zero. Every
right-hand side is an integer polynomial in retained coordinates at the
time it is used. Projection and the reverse restoration are inverse maps
on the two integer zero sets. There are now 23 coordinates and 11 rows,
precisely those in Section 2.

The final residual degrees are

    4,4,3,4,6,4,4,3,4,6,6.

In the guard, the leading contribution to zeta from jc is jc, so the
coefficient of `eta^2 j^2 c^2` in r11 is -1. Its square has coefficient
1 at `eta^4 j^4 c^4`. No other degree-six residual involves eta or j,
and no other monomial in r11 can contribute to this exact square without
introducing another variable or reducing the target exponents. The exact
sparse checker verifies the coefficient is literally 1 over the fixed-port
polynomial ring. This proves degree twelve for the actual six numerals.

More explicitly, the complete degree-twelve homogeneous part is

    256 beta^4 J^4 u^8 + I^4 f^4 o^4
       + eta^4(-fo+jc+hE)^4.

These are respectively the leading squares of the main Pell, auxiliary Pell,
and merged positivity residuals. The exact checker verifies this full identity,
not just the selected coefficient.

## 7A. A degree-ten equation in 24 integers

The 23-variable equation spends degree six on its merged guard because zeta
has been eliminated. For a lower-degree endpoint, start instead with P26 and
retain zeta. Eliminate D and V by the same monic definitions, and make the
integral coordinate shear `y_old=fo+y`. The auxiliary residual becomes

    Aaux=(fo+y)^2-I^2(c+y)(2fo+y-c)-1.                         (3)

This is exact because
`(fo+y)^2-(fo-c)^2=(c+y)(2fo+y-c)`. It has degree five, whereas direct
substitution of V into the uncentered auxiliary norm would have degree six.
The inverse shear is `y=y_old-fo`, so all integer witnesses are preserved.

The main norm is still apparently degree six after D is eliminated. Put

    Y=a-E, b=ac+gamma H, X=4q u^2,
    N=(X+b)^2-Delta c^2-1,
    M=XE+2Eb+Y[H(2ac gamma+H gamma^2-c^2)-1].                  (4)

The exact polynomial identity is

    M=Y N+(X+2b)(E-XY).                                     (5)

Indeed `b^2-Delta c^2=H(2ac gamma+H gamma^2-c^2)`. The retained row
`E-XY=0` therefore makes `M=Y N`. The retained scale row gives

    Y=(2v+1)q^3 != 0.

This nonvanishing requires no Pell theorem or sign assumption: `2v+1` is
nonzero for every integer v, and `q=beta J+1` cannot be zero because beta>1.
Thus on every common zero of the other retained rows, `M=0` is equivalent
to `N=0`. The replacement in (4) introduces no spurious component at Y=0.
It is essential to prove this nonvanishing; replacing an equation by an
arbitrary multiple would not generally preserve its zero set.

The complete P24 system has these twelve rows, with `k=eta+zeta`,
`V=fo-c`, `Delta=a^2+H`, and all other abbreviations as in Section 2:

    Y-(2v+1)q^3,
    E-XY,
    c-eta-kY,
    tau^2+(2tau-k)E(c-eta)-1,
    M,
    k-R-1-hE,
    (K0 q+X)C-qF-Z(q-1),
    k+V-cj-hE-1,
    I-(2r+1)c^2,
    I^2-Delta(f^2-1),
    Aaux,
    Pair(G,eta*zeta,t)-Pos(p1,p2,p3).

Its unknowns are those of P23 together with zeta. The root y has the centered
meaning specified above. Every residual has degree at most five. The complete
degree-ten homogeneous part of their sum of squares is

    64a^4 gamma^2(c+2gamma)^2(a-E)^2
       +4I^4 f^2 o^2(c+y)^2.

The terms come from M and Aaux. In particular the coefficient at
`I^4 f^2 o^2 y^2` is exactly 4, proving exact degree ten for all fixed ports.
The supplied evaluator uses 135 live binary gates. The construction has 24
integer unknowns and twelve residuals, and preserves solvability by the
coordinate shear, exact monic maps, and identity (5) with Y nonzero.

## 7B. A degree-fourteen equation in 22 integers

Start instead with P23. Make the same auxiliary-root shear `y_old=fo+y`.
Let

    Q=Delta(f^2-1),
    S=I^2-Q,
    Aold=y_old^2-I^2(y_old^2-V^2)-1.

Replace Aold by

    Anew=(fo+y)^2-Q(c+y)(2fo+y-c)-1.                          (6)

The identity

    Anew=Aold+S(y_old^2-V^2)                                (7)

shows that this is an invertible elementary row operation in the presence
of the retained strong norm S=0. In particular it preserves all common
integer zeros without a nonvanishing assumption or division.

Now I appears only in its monic definition and in the strong norm. Eliminate

    I=(2r+1)c^2.

The strong row becomes `(2r+1)^2 c^4-Delta(f^2-1)`, of degree six. The
new auxiliary row (6) has degree seven. All other rows are those of P23,
unchanged, and have degree at most six. The complete system therefore
consists of P23's first seven rows, its strong row with this substitution,
the row (6), and its merged positivity row. The I-definition row is deleted.
There are 22 integer unknowns and ten residuals; y has the centered meaning.

The only residual of degree seven is Anew. Its leading form is
`-2a^2 f^3 o(c+y)`. Thus the exact degree-fourteen homogeneous part of the
sum of squares is

    4a^4 f^6 o^2(c+y)^2.

The coefficient at `a^4 f^6 o^2 y^2` is exactly 4. The compact evaluator
uses 123 binary arithmetic gates. This is a variable/degree tradeoff with
P23, not a claim that one dominates the other.

Replacing I directly in the old auxiliary norm would produce a substantially
higher degree. The point of (7) is to remove I from that norm first, and the
root shear then cancels its leading square. These operations are certified by
exact polynomial identities and accompanied by explicit inverse witness maps.

## 8. Logical conclusion

For each of the five final equations, soundness first reconstructs the
positivity witnesses and the monically deleted coordinates. The determinant
then restores the source75 common-sign guards. Its signed bootstrap theorem
restores the source64/native arithmetic interface, whose calibrated
accepting computation yields a finite proof of contradiction in the fixed
recursive ZFC proof calculus.

For completeness, a finite ZFC refutation yields canonical native witnesses
under the inherited calibration. Source75 supplies its signed-bootstrap
coordinates; the native leading-digit bounds prove the determinant positive;
the nearest-square lemma and Pos theorem supply the merged guard witnesses.
The exact projections then supply zeros of each displayed smaller equation.

All new witness transformations and arguments are elementary and formalizable
in ZFC, and the imported source theorems are explicitly named ordinary
ZFC-formalizable theorems. Thus, with exactly the inherited syntactic
consistency predicate,

    ZFC proves:  (there is no integer zero of P) <-> Con(ZFC).

This states an equivalence within ZFC. It does not assert that this work proves
ZFC consistent or that searching a finite range verifies the equivalence.

## 9. Reproduction, finite checks, and costs

From this directory run:

    python3 build.py
    python3 circuits.py
    python3 verify.py

`build.py` reconstructs source75's signed40 and signed34 residuals from the
literal Q41 packet and checks both comparisons exactly. It checks each monic
elimination, all variable occurrences, the symbolic degrees and
fixed-port-independent leading coefficients, every pinned source byte, and
all six fixed integer payload hashes. `circuits.py` reconstructs the compact
formulas and compares every residual exactly with the literal packet. The
standard-library independent verifier additionally parses and evaluates the
delivered circuits and residual expressions by separate paths and recounts
their live gates. Normal and optimized Python runs retain validation.

The gate convention charges every live binary +, -, or * operation, including
scalar multiplication and squaring; fixed numeral leaves and reuse are free.
Identical commutative gates are shared. The totals, in increasing degree order,
are 144,131,135,122,123.
No optimality claim is made for these circuits. Expanded symbolic-port term
counts are 815,5653,5634,16360,16525; they are not asserted to equal term counts after all
large numerals have been combined. The six coefficient payloads total 615883
raw bytes, before compression, with a maximum input bitlength 1065043. Expanded
coefficients can be larger. Variable count, degree, arithmetic gates, and
coefficient bit size remain different notions of simplicity.

The universal compiler and Pell lemmas are mathematical dependencies, not
something the finite Python program proves. The new algebraic checks and
internal independent review do not constitute external human peer review.

## 10. Further questions

1. Can a different representation of the two required positivity conditions
   retain 23 integer variables while lowering degree twelve? In this family,
   elimination of zeta makes the current merged guard sextic; removing that
   bottleneck would require a new guard or a new arithmetic relation.
2. Can the strong-ordinate elimination of Section 7B be improved to degree
   twelve? The row operation and root shear reach degree fourteen, whereas
   direct substitution of I=(2r+1)c^2 gives a worse degree.
3. Can the weighted determinant be proved directly for a substantially smaller
   coherent native coefficient tuple, with a fresh calibration and explicit
   leading-digit estimates? Substituting a smaller tuple without this proof
   would be invalid.
4. Can the signed-bootstrap/determinant/nearest-square chain be formalized as
   reusable zero-set transfer theorems and then attached to a verified native
   compiler? The exact algebraic certificates already isolate the finite part.
5. Can the 122-gate expression be shortened while retaining this same polynomial
   or an equally simple equivalent one? Degree and variable-count reductions
   do not by themselves imply bit-complexity improvements.

