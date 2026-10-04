# A paid integer selector for the synchronized matrix substrate

The actual96-tile table now has a complete local predicate costing
**1714=859M+855A** over signed integers, or **1715=860M+855A** with an
exact existential interpretation over the reals as well. Both have exact
degree192 and use **one additional signed selector witness** per step.
Their full ordinary-input countdown extensions cost **1740=871M+869A**
and **1741=872M+869A**, respectively, with exact degree194.

Relative to [grouped row choices](matrix193_grouped_row_choices.md), this
saves301 or300 arithmetic operations in each complete local predicate.
It trades an extra witness and larger fixed numerals for fewer operations.
Unbounded history packing and conversion of signed states to positive
witnesses remain unpaid. This is not a new universal-polynomial bound;
the established84-operation construction remains unchanged.

## 1. Exact source and coefficient convention

The [fresh helper](matrix193_newton_selector.py) authenticates the grouped
and countdown parent trios using six SHA256 pins stored in the
[receipt](matrix193_newton_selector.json). Every predecessor is inert data;
no old Python, builder or historical simulation is imported or executed.
The receipt emits all four complete instruction arrays, selector-to-tile
maps, coefficient tables, live-port ledgers and degree certificates.

Use the same fixed signed-integer numeral convention as the parent table:
fixed literals are free leaves, but multiplication of any nonconstant
register by a fixed numeral costs one operation. Negative coefficients,
integer subtraction and all eight matrix-entry producers are charged.
This is not the ant's restricted literal1/3 coefficient grammar or a
bit-operation count. The common scale below has492 bits; the largest
scaled Newton coefficient has574 bits. Both sizes are recorded explicitly.

The new selector z is distinct from the actual tile identifier. Label the
96 rows by0,...,95 after moving tile IDs109,110,111,112 to the front in
that order and retaining the relative order of all other rows. These four
tiles have the same upper K matrix and distinct lower actions. Every old
tile appears exactly once, and each label still chooses its matched pair
(K_j,G_j). There is no independent upper/lower branch selection.

## 2. Integer-scaled Newton lookup, with every operation paid

Let D=95!, P_0(z)=1 and

    P_j(z)=product_(0<=k<j)(z-k),  1<=j<=96.

The source shares every P_j and every shift z-k across all eight matrix
columns. For a column of actual integral values v_0,...,v_95, let Delta^j
v_0 be its j-th forward difference. The emitted integer polynomial is

    L_v(z)=sum_(j=0)^95 [D*Delta^j(v_0)/j!]*P_j(z).

Every bracket is an integer because j! divides D. Finite-difference
interpolation gives L_v(j)=D*v_j at every label j. There is no variable
division or uncharged interpolation oracle in the evaluated source: the
table determines fixed coefficients effectively, and all nonconstant
products and sums appear in its literal instruction array.

The helper independently expands the97 entire falling-factorial
polynomials and all eight lookup polynomials, checks their degree bounds,
and verifies768 exact node values against the original table. Degree at
most95 together with96 distinct node values establishes the complete
lookup polynomial, not merely agreement on a sample of unspecified size.
Each actual lookup has degree95.

Putting the four identical K rows first makes forward differences1,2,3
zero in each of the four K columns. Those twelve omitted terms save12M
and12A. There are no other zero nonconstant coefficients in the chosen
ordering. A generated, live comparison source in the original row order
costs1738/1739; its source hash and counts are saved, while complete row
arrays are emitted for the optimized variants. No optimality over all
row orders or all lookup constructions is claimed.

## 3. Exact existential transition relation

Write the supplied current rows as X=(x0,x1), Y=(y0,y1), and next rows as
X',Y'. Let L_K(z),L_G(z) be the two2x2 arrays of scaled lookup entries.
The four paid scalar residuals are precisely the coordinates of

    DX' - X L_K(z),   DY' - Y L_G(z).

Write E for the sum of their four squares, and Q=P_96. The real-safe
local polynomial is

    P_real=Q(z)^2+E.                                    (1)

For arbitrary real supplied coordinates, its zero forces Q(z)=0, hence
z is one of the96 integer labels. The scaled lookup then gives the exact
matched action, because D is nonzero. Conversely any original tile step
has a zero by choosing its label. Thus, after existentially quantifying
the single selector, (1) has exactly the parent's real transition relation.
In particular it has the same integer relation.

On the signed-integer selector domain one multiplication can be omitted:

    P_integer=Q(z)+E.                                   (2)

For every integer z, Q(z)>=0. It is zero at0,...,95; for z>=96 all
96 factors are positive, and for z<0 all96 factors are negative, with
positive product. Consequently (2)=0 also forces Q=E=0. This is an
integer-domain proof; Q is not nonnegative on all real numbers.

Indeed at z=1/2, Q<0. Set both current rows and all next coordinates to
zero except next_x0=sqrt(-Q)/D. Then (2)=0, although no matrix maps the
zero current row to that nonzero next row. This exact counterexample
explains why the one-operation improvement is restricted to integers.
The two variants are neither all-value equal to their parents nor exact
positive-witness charts. Their stated equivalence is existential over the
extra selector on the stated domains.

The helper separately expands the entire paid residual/finalizer portion
at eight independent lookup ports, checking all25 coefficients against
(1) or(2). Thus the node-value test is connected to every actual state
coordinate and the whole final output, rather than to an isolated lookup.

## 4. Counts and exact degrees

The shared shifts and prefixes cost95M+95A. After the twelve zero terms
are removed, the eight lookups cost748M+748A. The four residuals, their
squares and the joins cost16M+12A. Squaring Q costs one further M only
in the real-safe variant. Therefore the complete counts are:

| Interface | M | A | Total | Extra selectors | Exact degree |
|---|---:|---:|---:|---:|---:|
| Integer synchronized |859|855|1714|1|192|
| Real-safe synchronized |860|855|1715|1|192|
| Integer countdown |871|869|1740|1|194|
| Real-safe countdown |872|869|1741|1|194|

Every source row and free port is live. Relative to grouped choices, the
integer variant saves244M+57A; the real-safe variant saves243M+57A.
The additional selector is explicitly counted rather than treated as a
free fixed index or an external branch oracle.

All lookup entries have degree95 in z. Each state residual has degree at
most96, so the synchronized degree is at most192. To prove attainment on
the complete source, set z=x0=t and every other supplied port to zero.
The two upper-row squares have leading coefficient equal to the sum of
the squares of the nonzero leading coefficients of L_K0 and L_K1.
This is positive. Adding Q² adds another positive leading coefficient
in (1); adding degree96 Q cannot cancel it in (2). Both degrees are192.

The saved dense univariate execution evaluates every row on this line,
records the exact leading coefficient and hashes the full polynomial.
It is a complete source degree certificate, not a sampled evaluation or
an equation used only at zeros.

## 5. Countdown, ordinary input and fixed-duration cost

The inherited26-row extension is copied with only its tile-output wire
changed. Its polynomial is exactly

    E_load * (P_local+n²+(n')²),

where E_load is the original sum of five squared loader residuals, with
the same fixed B-inverse action. A separate independent62-coefficient
expansion verifies this entire wrapper and each of its two factors.

On the stated domain P_local>=0. A zero is therefore either the original
LOAD action, or an original matched TILE with both n=n'=0. In a LOAD
step the selector is unrestricted and can always be chosen as integer0.
The original zero-gate initialization starts n at the ordinary input x,
so every accepted finite word remains `LOAD^x TILE*`, even with signed
counters. All state and endpoint arguments from the countdown parent
are retained. No outside Pell-index relation is added.

For the countdown degree line also set n=t and n'=0. Then
E_load=t²+(t-1)², while the tile factor is the synchronized polynomial
plus t². Its positive degree194 leader is verified through every paid
instruction. The integer-domain restriction of (2) does not alter this
formal polynomial-degree calculation.

For fixed h>=1 steps, the integer schedule gives **1741h+7 operations
and6h signed integer witnesses**, with degree at most194. The real-safe
schedule gives1742h+7 with the same witness count. These bounds pay h
joins and the unchanged7-gate endpoint. The analogous supplied-target
synchronized bounds are1715d+5 and1716d+5 with5d signed witnesses.
No exact degree after arbitrary initial substitutions is asserted.

This remains a fixed saved matrix context. The interpolation transformation
works for any finite table, but neither the96-label count nor the12 zero
coefficients is claimed for every program context. An arbitrary-duration,
fixed-witness Diophantine packing still needs its complete cost and proof.

## 6. Bounded validation and replay

The receipt preserves four full arrays, exact lookup/coefficient proofs,
all-row liveness, both finalizer proofs and all degree lines. Its794
whole-source checks cover every actual tile, deliberately wrong next rows,
outside-range selectors and loader steps, plus rational non-label selectors
for the real-safe variants. These examples supplement the unrestricted
domain-specific proofs, not a historical trace rerun.

    python3 matrix193_newton_selector.py --root /absolute/native-stream-queue --expect matrix193_newton_selector.json
    python3 -O matrix193_newton_selector.py --root /absolute/native-stream-queue --expect matrix193_newton_selector.json

All checks use explicit exceptions under both modes, and receipt replay
compares exact generated bytes. Duplicate/noninteger JSON fields in pinned
receipts are rejected. No maintained public compiler API, global circuit
minimum, positive-witness conversion or new universal bound is claimed.
