# Complete ordinary-input tag compilation with a shared counter scale

The dyadic recoder, fixed-block counter loader and selected tag history
now compose into one complete positive Diophantine source. The default
illustrative family has a **399=194M+205A** polynomial, **69 positive
existential witnesses**, and exact degree **4452**. Its certificate
costs **325=169M+156A**, with **25 comparisons**. A supplied initial
history value gives **402 operations**,70 witnesses and degree1620.

This example is a fixed tag-word family, **not a numerical universal
machine instance**. The generic compiler applies to the word format of
the proved clockwise/tag bridge. Instantiating a fixed universal table
and its program interface remains necessary before reporting a new
numerical universal bound. The separate established75/87 frontier is
unchanged.

The [source](binary_tag_complete_dyadic_compiler.py) and
[receipt](binary_tag_complete_dyadic_compiler.json) retain three complete
forms: raw SOS, safely regrouped native units, and three normalized
strong witnesses. Every source uses the paid dyadic-duration recoder.

## 1. Exact fixed-word family and positive-input contract

Fix a binary tag system with deletion beta>=2 and productions
`b -> b`, `c -> u`. Require nonempty u ending in b and
`|u|=1 mod(beta-1)`. Fix b/c words

    PREFIX, DATA_0, DATA_1, MIDDLE, MU, TAIL.

The two DATA words and MU are nonempty. TAIL is nonempty and ends in b.
The DATA words have the same counts of b and c. Let the binary encoding
be `e(b)=10^beta1`, `e(c)=1`, and let
`E(TAIL)=e(TAIL without its last b)10^beta`. Put

\[
 D=|e(\mathrm{DATA}_i)|,\quad t=|e(\mathrm{MU})|,
 \quad D=mt,\quad m\in\mathbb Z_{>0}.
\]

The constructor checks t divides D and the fixed length congruences

\[
\begin{aligned}
 |\mathrm{PREFIX}|+|\mathrm{MIDDLE}|+|\mathrm{TAIL}|&\equiv1
                                                   \pmod{\beta-1},\\
 |\mathrm{DATA}_0|+m|\mathrm{MU}|&\equiv0
                                                   \pmod{\beta-1}. \tag{1}
\end{aligned}
\]

For a padded length-n binary spelling `w=w1...wn` of the positive input
x, define the actual tag word

\[
 W(w)=\mathrm{PREFIX}\,
 \mathrm{DATA}_{w_1}\cdots\mathrm{DATA}_{w_n}\,
 \mathrm{MIDDLE}\,\mathrm{MU}^{mn}\,\mathrm{TAIL}.       \tag{2}
\]

The compiled positive-input language is **exactly**

\[
 \{x>0:\text{for some dyadic }n\ge2,\ x<2^n,
       \text{the tag system halts on }W(\operatorname{bin}_n(x))\}. \tag{3}
\]

Input duration n and selected history duration are independent
existential quantities. There is no external word or bit oracle in (3).
If a machine bridge proves that these padded words all simulate the
same input computation, the existential choice in (3) therefore preserves
that machine's ordinary-input language.

Every word (2) ends in b and has length1 modulo beta-1. Its length is
strictly greater than1: each data/counter block contributes a positive
multiple of beta-1, and n>=2. More precisely, the fixed framing has
positive length congruent to1 and the total length is at least
`1+2(beta-1)`. Thus the word is not the initially halted singleton and
has length at least beta. The two-operation singleton branch of the
encoded-tag predicate is unnecessary here.

On this slice tag length stays positive and1 modulo beta-1, and the
last letter remains b. Consequently every halt is the singleton b.
The [four-tile theorem](binary_tag_four_tile_history.md) therefore gives
halting iff a **nonempty** selected tile history matches the endpoints.
Its soundness proof allows an algebraic tile word to consume future
production letters after a short queue: it stops at the first actual
halt, rather than falsely asserting legality of every remaining block.

## 2. Paid recoding and loading

The [dyadic-duration recoder](native_binary_dyadic_duration_recoder.md)
at width D supplies exactly

\[
 n\ge2\text{ dyadic},\quad 0<x<2^n,\quad
 Q=2^{Dn},\quad z=\operatorname{spread}_D(x).           \tag{4}
\]

It retains two native kernels, the synchronized repunits, both ratio
slacks and the low-block AND test for the actual duration. Its output z
is an additional positive existential coordinate in the whole compiler.

Apply the [shared counter loader](binary_tag_shared_counter_loader.md)
to the binary fixed blocks

    e(PREFIX), e(DATA_0), e(DATA_1), e(MIDDLE), e(MU), E(TAIL).

One new positive r and the comparison `(2^D-1)r=Q-1` supply both the
data repunit and counter repunit. The folded output costs eight gates,
including that comparison's multiplication:

\[
                       V_i=(Ar+Bz)Q+Tr+E.              \tag{5}
\]

Here A,B,T,E are the fixed numerals explicitly defined by the loader.
Equation (5) is exactly the positive sentinel integer `code(E(W(w)))`
on (4) and the repunit comparison. Its direct-concatenation correction
off that comparison is retained in the loader proof and tests.

For computed Vi the API requires `val(e(DATA_1))>=val(e(DATA_0))`, so
B>=0 and (5) is positive on every positive tuple, even before typing.
The actual clockwise/tag format has strict inequality, proved in
[input normalization Section5](clockwise_dyadic_input_normalization.md#5-the-ordinary-data-coefficient-is-strictly-positive).
The supplied-endpoint API instead introduces positive `tag_value` and
retains `Vi=tag_value` as an extra comparison. It permits either data
ordering. This is a genuine one-witness/one-comparison interface choice.

Optional program loaders are fully paid. A fixed positive code C uses
`y=(2C)x+C` in1M+1A; a supplied positive code p uses
`y=p*(x+x+1)` in1M+2A. The recoder then uses y everywhere in place of x.
The represented family is (3) with y substituted. A universal interpretation
of particular p slices still requires a fixed recognizer that decodes
that pairing; the arithmetic option alone does not instantiate one.

## 3. Complete history and raw positive equivalence

The four actual tiles of the fixed tag system give four affine append
maps. Their selected history starts at `(1,Vi)`. Its terminal boundary is

\[
                        V_f=2^{\beta+1}U_f+2^\beta,    \tag{6}
\]

computed in two paid gates. The native selected-history source pays
every selection, product, range, time and scale relation; it quantifies
only positive witnesses. The builder aliases its input to (5), or to
the separately supplied endpoint, and prefixes every history register
and witness with `hist__` to avoid collisions. Each source dependency
and coordinate domain is checked topologically.

At a raw positive zero all residuals vanish. The independent recoder
theorem first gives (4). The loader then gives the exact word sentinel,
and the complete positive history theorem gives a nonempty matching
tile word. The four-tile theorem implies actual halting. This proves
soundness of (3) without assuming input/history durations equal.

Conversely, choose a dyadic n and a halting run in (3). The recoder's
complete canonical converse supplies all its positive auxiliaries at
that n. The unique positive r gives (5). The genuine nonempty halting
trace gives a selected tile word, and the complete history converse
supplies fresh positive auxiliaries at its independent history scale.
Its actual endpoint satisfies (6). The namespaces share only the
already fixed positive input value. These extensions therefore coexist
and make every raw residual zero.

The sum of squares of all raw residuals is one polynomial with exactly
the same positive zero projection. No full astronomical native Pell
tuple is claimed to be materialized by the finite fixtures.

## 4. Safe units and three strong normalizations

The optional [complete native-unit rewrite](gpcp_complete_fixed_program_units.md)
applies to the literal three native cores. The dyadic recoder's changed
ports retain their positivity; its dedicated
[unit proof](native_binary_dyadic_duration_units.md) checks the joined
F3 field, packed index and duration comparisons explicitly. The loader
and optional program equations are retained. Definition projection and
positive root gaps restore the raw source before invoking its theorem.

The global ten-factor product consists of nine independently sign-safe
native norm factors and **one** unrestricted recoder checksum. The
history checksum remains a **separate comparison**. Thus the two
unrestricted checksum signs are not silently merged. The finalizer is

\[
                  W\left(1+\sum_j R_j^2\right)-1.      \tag{7}
\]

An integer zero forces W=1 and every retained residual to vanish.
The native sign and positive-coordinate arguments then restore exactly
the raw certificate. Its positive converse is the existing projected
coordinate construction. This option removes19 witnesses and28
comparisons while adding9 multiplications to the certificate.

The default [three-core strong normalization](gpcp_normalized_strong_compiler.md)
then appends one sign-safe Pell factor per core, removing only its strong
comparison. At a zero, `i_old=Delta*i` simultaneously restores those
three old equations and their auxiliary coefficients. All restored
coordinates are positive before native typing, including the history
input in either supported endpoint interface.

For the converse, each native theorem identifies its own actual
`Jnative=2r+1=3 mod4`. Rebuild only f,i,j,o,y in that core using the
canonical index `m=2c*Jnative`. Divisibility `c^2|psi_A(m)` and the
retained minus congruences give positive integers. The inherited
transitive dependency audit verifies that these fifteen fields change
no loader, duration, word, endpoint, ratio bound or checksum. Thus the
normalized source has the same accepted inputs, although it is not
an off-zero polynomial identity or a bijection of all witness tuples.
It adds6 certificate multiplications and removes3 comparisons, saving
three polynomial operations.

## 5. Literal costs and exact degrees

For the four illustrative tables the selected affine history has
H=161 operations and scale exponent N=11. Put
`mu(D)=floor(log2 D)+popcount(D)-1`. With a computed endpoint and no
program loader, the full raw certificate costs307+mu(D) operations,
56 comparisons and88 witnesses. The unit version costs316+mu(D),
28 comparisons and69 witnesses. The normalized version costs322+mu(D),
25 comparisons and69 witnesses. Their polynomial counts are respectively

\[
              474+\mu(D),\quad399+\mu(D),\quad396+\mu(D). \tag{8}
\]

These formulas use the actual H=161 history schedule, rather than
assuming every conceivable fixed tag table has that ledger. More
generally replace161 by the actual H: the three polynomial costs are
`313+H+mu(D)`, `238+H+mu(D)` and `235+H+mu(D)` when the same four-tile
history geometry and comparison counts apply. Every returned ledger
counts its actual source. A supplied endpoint adds one witness, one
comparison and three polynomial gates. Fixed/supplied program loaders
add2/3 gates and preserve those witness/comparison counts.

The example uses beta3,u=`ccbbb`, DATA0=`bc`,DATA1=`cb`,MU=`c`, and
PREFIX=MIDDLE=TAIL=`b`. Hence D=6,m=6 and mu(D)=3. These are illustrative
fixed words, not a universal machine table.

|Form|Certificate|Comparisons|Witnesses|Polynomial|Exact degree|
|---|---:|---:|---:|---:|---:|
|Raw, computed|310=154M+156A|56|88|477=210M+267A|1072|
|Units, computed|319=163M+156A|28|69|402=191M+211A|2792|
|Normalized, computed|325=169M+156A|25|69|399=194M+205A|4452|
|Raw, supplied|310=154M+156A|57|89|480=211M+269A|280|
|Units, supplied|319=163M+156A|29|70|405=192M+213A|980|
|Normalized, supplied|325=169M+156A|26|70|402=195M+207A|1620|

For the raw source let nu=D+2 for computed Vi and nu=2 for supplied Vi.
Its exact degree is `max(12D+40,12N*nu+16)`. The supplied-program
multiplication does not alter the raw q coordinate's degree before
projection.

For either unit source let e=2 for the supplied multiplicative program
code, otherwise e=1, and put

\[
 v=(2D+1)e+1,\quad
 \nu=De+2\text{ (computed), or }2\text{ (supplied)},\quad d=N\nu.
\]

The old-strength product degree is
`14e+19v+2De+20d-6nu+64`, and its largest retained residual degree is
`4max(v,d)+10`. After normalization these become

\[
 D_W=30e+35v+2De+36d-6\nu+142,\qquad
 M=\max(3v+De+1,4d-3\nu+1).                         \tag{9}
\]

The exact degree in each case is product degree plus twice the largest
residual degree. These are degrees of the literal composed polynomial,
not degrees after imposing any equation. All three main-norm
cancellations have their source rows and strict highest-term inequalities
checked before the override is applied. All other degrees propagate
through the actual arithmetic. A nonzero weighted highest coefficient
proves attainment. Two independent actual factor/residual polynomial
evaluations additionally verify the degree and leading coefficient.

## 6. Evidence and remaining universal instantiation

The checker audits73 interface/table/form ledgers,576 complete output
identities including288 signed cases,44 literal framed inputs and24
genuine halting-history outer compositions. The latter compare actual
tag steps, tile words, affine endpoints and paid recoder/loader values;
native auxiliaries remain explicitly unmaterialized. The reversed-block
computed interface is rejected, and its supplied counterpart is covered.
The three-core normalized audit composes the strong corrections with
the complete raw-unit lift rather than equating different off-zero
polynomials.

```sh
/tmp/diophantine-research-venv/bin/python binary_tag_complete_dyadic_compiler.py
```

For the clockwise normalization format, D=2azK and m=2a, and dyadic
n>=2 gives the exact required counter c0=2an. Its word congruences and
data coefficient order satisfy this builder's contracts. The parametric
composition therefore closes its arithmetic interface for each fixed
machine after the fixed constants are supplied. A numerical universal
claim still needs one instantiated universal table, exact encoding-width
metadata and a paid valid program-slice interface. No such numerical
claim is inferred from the small example or from formula (8) alone.
