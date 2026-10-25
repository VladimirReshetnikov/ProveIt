# Symmetric low-digit budgets for direct ZFC consistency equations

Prepared with AI assistance for Vladimir Reshetnikov and ProveIt, 25 October 2026.

## 1. Results, domains, and precise dependency

The equation in each endpoint directory is the sum of squares of every listed
quadratic residual in `equation.json`. All coordinates range independently
over **unrestricted integers**. Its adjacent `expanded_polynomial.json` gives
the complete collected polynomial. No variable exponent, factorial, binomial,
or unspecified coefficient is an operation in these literal equations.

The basic construction gives 261 variables and 185 residuals. Merging the two
neighboring digit levels gives 260 variables and 186 residuals. A compatible
odd-square radix gives 258 variables and 186 residuals. Their exact degree is
four. Integral coordinate translations and any separately certified invertible
residual-row operations preserve their zero sets.

The inherited source is exactly `direct/strict_dimension/guarded.json` in
`ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25.zip`, present in ProveIt
commit `e0c98c629bf10d30b695884f6b1d2ab361bdf513`. The original endpoint is the
282-variable direct quartic. The source and its source-change certificate
are copied into `inherited/`; the delta certificates bind their entire bytes.

The inherited ordinary proof consists of `PROOF_315.md`,
`ORIENTATION_FIRST_PROOF.md`, `STRICT_BUDGET_PROOF.md`, and their retained
round-16 and round-15 arithmetic/calibration dependencies. Those proofs give
the numerical C222 derivation equivalence, and the two named logical
interfaces are `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.

The new argument below is an ordinary proof formalizable in ZFC that each
new polynomial has an integer zero exactly when a finite ZFC refutation
exists. Its negation is therefore the requested ZFC-provable equivalence
between integer unsolvability and Con(ZFC). This is not a proof of Con(ZFC),
a global simplicity theorem, or a new end-to-end Lean/Rocq certificate.

## 2. Literal deletion boundary

The parent retains eleven interval conditions of the form

    D_i = r_i + s_i + 1,
    r_i*s_i = a_i^2+b_i^2+c_i(c_i+1).

The second row, by itself, says `r_i*s_i >= 0`; once `D_i>0` is known, the
first row then gives both `r_i>=0` and `s_i>=0`. Each such guard costs three
private integer coordinates. The present transformation removes precisely
these eleven **product-guard rows**, retains their linear remainder-bound
rows, and introduces four shared squared budgets. Their three auxiliary
coordinates each give twelve new coordinates in place of thirty-three.

The three front sign guards on `fact0.remainder`, `fact0.slack`, and
`choose0.oslack` initially remain. The first two belong to the ceiling
identity; they are different from the low-digit remainders being pooled.
Every Pell norm, frame row, semantic anchor, orientation residue, exact-power
request, CRT equation, and Horn-calculus equation remains unchanged.

The groups, with the parent source variable names, are:

| Group | Denominator | Remainders |
|---|---|---|
| `t` | `pow4.output = q^t` | `choose0.remainder`, `range8.remainder` |
| `tplus1` | `pow6.output = q^(t+1)` | `range0,1,2,3,9.remainder` |
| `yplus1` | `pow11.output = q^(y+1)` | `range4,5.remainder` |
| `x` | `pow14.output = q^x` | `range6,7.remainder` |

Here `q=pow2.output`. Powers in this table describe the proved semantics of
existing quadratic graphs, not operations added to the polynomial.

For each group G with denominator D, insert the quadratic residual

    D^2 - 4*sum(r_i^2 : i in G) - 1 - u^2 - v^2 - w(w+1).

The ternary expression `u^2+v^2+w(w+1)` is nonnegative for all integer inputs
and represents every nonnegative integer. The latter follows from the
three-square theorem applied to `4n+1`: exactly one represented coordinate
is odd and the other two are even, yielding the displayed form after
division by four. This representation fact is already used in the parent.

## 3. Exact-power recovery remains earlier than digit signs

This section refers first to the 261- and 260-variable versions, which retain
all three old front sign guards. The signed semantic anchor and the pooled
orientation equation of the parent identify both coordinates of every
principal Pell pair before any low-digit remainder signs are used. The
parent's strict-budget proof then recovers all eighteen actual powers before
the eleven interval signs. None of the rows removed here participates in
that recovery.

At that stage the following facts are available, **without yet assuming
F=t! or any binomial interpretation**:

    t >= 16,  F >= 1,  B >= F+1 >= 2,
    V0 = (F^2+1)^t,
    y = V0(V0-1),
    x >= 2+(t+1)y,
    a_1,...,a_9 >= 0,
    H0 = 1+sum a_i >= 1,
    q = (B*H0)^x >= 2.

In detail, the ceiling signs give `F*B=V0+s` with `s>=0`; thus `B>F`.
The first and last beta endpoints then give the stated lower bound on x.
The requests at base `q+1` force the nine actual representatives nonnegative,
including the possibility of zero. The nominal derived-label index h is
positive by its own oriented request and the nonzero semantic-anchor bound.

Let `ell=4194304=2^22`. The inherited monotone constructor ledger gives

    h <= (n*+1)^ell,
    n* = max(1,a,b,c,d),

where a,b,c,d are four of the nine actual representatives. Since
`n*+1 <= 2H0` and `B>=2`, this implies

    h <= (2H0)^ell <= (B*H0)^ell.

This bound is valid even if H0=1. It does not use the later nonzero encoded
index argument or the factorial interpretation.

The two useful exponent gaps follow already from these raw facts. Since
`V0 >= 2^t`,

    y >= 2^t(2^t-1) > ell    (t>=16),
    y >= t+2.

Consequently

    x >= ell*t+4,
    x >= t(t+1)+4.

For the first inequality use `y>=ell+1` in `x>=2+(t+1)y`; for the second use
`y>=t+2`. These are intentionally coarse inequalities with substantial
slack. No fact about a hypothetical refutation's size is being assumed.

## 4. Uniform low-digit bound before the factorial fixed point

We prove that every relevant binomial coefficient below its requested digit
position satisfies

    binom(n,j) <= q/16.                                   (1)

There are three kinds of upper index n.

**Ordinary representative.** Every `0<=n<H0`. Each denominator exponent k
is at most x: the two strict beta quotient ranges use k=x, and the others
use t, t+1, or y+1, all below x by the endpoint lower bound. For `0<=j<k`,

    binom(n,j) <= max(1,n)^j <= H0^x <= q/16,

because `q=B^x H0^x`, `B>=2`, and `x>=4`. This includes n=0 and j=0.

**Derived-label representative.** Its denominator exponent is t+1, so
`0<=j<=t`. The preceding constructor bound and exponent gap give

    binom(h,j) <= h^j <= (B*H0)^(ell*t)
                <= (B*H0)^(x-4) <= q/16.

**Factorial upper index.** Here n=F^2+t and the denominator exponent is t.
For B>=F+1>=2 and t>=16 one has `F^2+t <= B^(t+1)`: for example
`F^2 < B^2 <= B^t`, `t <= 2^t <= B^t`, and `2B^t <= B^(t+1)`.
Thus, for all `0<=j<t`,

    binom(F^2+t,j) <= (F^2+t)^t <= B^(t(t+1))
                     <= B^(x-4) <= q/16.

This completes (1) using only the pre-factorial stage. In particular, the
proof does not establish digit signs by assuming the factorial conclusion
that needs those same signs.

## 5. Symmetric residue recognition

Fix any group denominator `D=q^k`, k>=1. For an upper index n>=0, let

    rho(n,k) = sum_{j=0}^{k-1} binom(n,j) q^j.

The binomial theorem gives `(q+1)^n = rho(n,k) modulo D`. From (1),

    0 <= rho(n,k)
      <= q(D-1)/(16(q-1))
      <= (D-1)/8 < D/8.                                  (2)

An arbitrary zero of the new group residual satisfies

    D^2 - 4*sum r_i^2 >= 1,

because the ternary expression is nonnegative. Hence `|r_i|<D/2` for every
member of the group. The retained exact numerator rows say

    r_i = (q+1)^(n_i) modulo D.

For the factorial digit, its high part is `D*(B+q*high)`; for a range test,
it is `D*N*quotient`. Both are literal multiples of D, regardless of the
unvalidated quotient signs. Thus `D` divides `r_i-rho(n_i,k)`. But by (2),

    |r_i-rho(n_i,k)| < D/2+D/8 < D.

The difference is zero. Every low remainder is therefore its correct
nonnegative canonical value. The retained row `D=r_i+s_i+1` now gives
`s_i=D-1-r_i>=0`. The old product guards can be restored with fresh ternary
witnesses.

All subsequent inherited arguments apply: the exact factorial digit and
ceiling identify F=t!; the amplified CRT range conditions decode genuine
nonnegative local parameters; the unit-weight Horn argument yields a finite
C222 derivation and hence a finite ZFC refutation. This is the soundness
direction for the complete new polynomial.

For completeness, start with any finite refutation and take the parent
construction's true semantic witnesses. Their canonical low remainders
satisfy (2). A group has at most five members, so

    4*sum rho_i^2 < 4*5*(D/8)^2 = 5D^2/16 < D^2.

Since the difference is an integer, `D^2-4sum rho_i^2-1>=0` and has a
ternary representation. Fill that representation and keep all other source
witnesses. This constructs a zero of the new graph.

## 6. Merging the adjacent t and t+1 levels

There are only two remainders at level t. Introduce two quadratic product
rows

    z_0=q*r_0,  z_1=q*r_1,

and combine z_0,z_1 with the five remainders at level t+1. The common
denominator is `D'=q^(t+1)=q*D`. The new group has seven entries, so replace
both old group guards by

    D'^2 - 4*(z_0^2+z_1^2+sum five_other_r_i^2) - 1
       = u^2+v^2+w(w+1).

Soundness gives `|z_i|<D'/2`, hence `|r_i|<D/2` because q>0. Section 5
then applies at each remainder's original denominator. Completeness gives
`q*rho_i<D'/8` for the two scaled residues and the same bound for the other
five. Consequently the combined squared sum is below `7D'^2/16<D'^2`.

The merger replaces six guard auxiliaries by three and adds two product
coordinates. It saves one independent coordinate. The literal measured
endpoint has 260 variables and 186 quadratic residuals.

## 7. An odd-square radix replaces one front sign guard

For the 258-variable form, additionally remove the front ternary sign graph
on `choose0.oslack` and impose the quadratic row

    q=(2z+1)^2.                                           (3)

This removes three private guard coordinates and adds one signed coordinate.
It restricts the raw witnesses, so both soundness and completeness need a
new argument. The argument does not require an odd-square assertion about
every old zero.

**Soundness bootstrap.** Equation (3) initially gives q>=1. Both coordinates
of every principal Pell pair are already canonically oriented by the
unchanged signed anchor and orientation rows; that proof uses the square
frame, not any sign of q or o. Interpret the request
`V0=(F^2+1)^t` directly. Its exponent t>=16 is already positive, and its base
is at least one. The base-one case is exact by the same canonical polynomial
congruence and frame bound. The retained ceiling signs give F>=1, B>F>=1,
and the same positive value y=V0(V0-1).

The strict-budget source has a genuine request at base B and requested
exponent x: `N=B^x`. The signed-power lemma for B>=2 forces x>=0 before any
arithmetic sign is assumed for x. The first endpoint then gives
`x>=F+1>=2`, and the last gives `x>=2+(t+1)y`. The numerator requests have
base q+1>=2, so they force the nine actual representatives nonnegative and
h nonnegative; the anchor makes h nonzero. Thus H0>=1, and the request at
base BH0>=2 now yields

    q=(BH0)^x >= B^2 > B.

The retained digit-output relation `q=B+o+1` consequently gives o>=0. Every
old front sign has been recovered, and q>=2 is available for all remaining
power and digit arguments. Sections 3-6 apply unchanged. The recovery order
is acyclic: (3), canonical orientation, V0, B, B^x, x, q+1 numerators, H0,
then (BH0)^x and q>B.

**Completeness parity choices.** In a true refutation construction, take
F=t! with t>=16. Put V0=(F^2+1)^t and y=V0(V0-1), so y is even. Every beta
CRT modulus `1+(i+1)y` is odd. Adding their odd product to a beta code
switches its parity; by choosing a sufficiently large even code, all
nonnegative quotient and endpoint requirements remain valid. Thus x may
be chosen positive and even.

For each `1<=i<=t`, the exact factor `d_i=1+F^2/i` is odd: because i divides
F, `F^2/i=F*(F/i)` is even. Hence B=product d_i and N=B^x are odd. The
independent representative CRT moduli have product N^2, which is odd, so
each representative's parity can be prescribed independently.

Prescribe opposite parities to a and b, as the parent semantic-anchor proof
requires; its literal parity identity then makes h even. Prescribe the
parity of one other independent representative so that the total of all
nine representatives is even, making H0 odd. There are seven representatives
outside a,b, so these requirements are compatible. Keep all ordinary
representatives in `(0,2N^2]` by their usual parity lifts. Choose the dominant
a representative by `a=a0+2N^2` or `a=a0+3N^2`, obtaining its required parity
and the unchanged bound `2N^2<=a<4N^2`. Thus the dominance, frame, and odd
anchor-completion bounds remain precisely the parent's ones.

Now B and H0 are odd and x is even. Therefore `q=(BH0)^x` is an odd square,
and the integer `z=((BH0)^(x/2)-1)/2` supplies (3). All low-digit budget
completions from Sections 5-6 remain valid at these witnesses. This proves
completeness of the 258-variable form.

## 8. Finite compilation and verification

`build.py` reads only the literal inherited guarded source and its named
guard metadata. It records every removed row, every new group and auxiliary
coordinate, the two optional scale products, and the optional odd-square
row. It then applies the inherited exact Horn factorization, followed by
integral monic elimination that never raises residual degree above two.
`projection_certificate.json` records a polynomial restoration for every
deleted coordinate. Unused old private auxiliaries are explicitly recorded.

The optional coordinate translations are integer bijections. The final
coefficient list is obtained by exact integer expansion of the sum of
residual squares. These are finite identities that can be replayed without
assuming the consistency or inconsistency of ZFC. They supplement, and do
not replace, the unbounded proofs above and the stated inherited calibration.

## 9. Attribution and further questions

The direct C222 arithmetic, semantic anchor, signed Pell orientation, and
strict exponent x are inherited. The incoming graph-digits package used
pooled **nonnegative** low remainders in a different natural-number compiler.
The present signed construction uses symmetric bounds, recovers each sign
from exact modular uniqueness, and proves the needed radix margin before
the factorial fixed point. No claim of global priority for Euclidean
remainder uniqueness, sums of squares, or parity-selective CRT is made.

Further questions include whether all four digit scales can share a single
quadratic budget without paying more product coordinates than it saves;
whether an additional cofinal arithmetic choice can remove either of the
two remaining ceiling sign graphs; whether a different source proof
calculus reduces the number of genuine power requests; and whether the
ordinary C222-to-polynomial chain can be formalized end to end in Lean or
Rocq. Each question concerns an unproved further reduction, not a property
silently used by the present equations.
