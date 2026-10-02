# A complete 425-operation universal equation with a fused query endpoint

> The [product-scale successor](tseytin_product_scale412.md) gives412
> operations and degree at most5662 with the same65-witness interface.
> Repunit sharing and recovered endpoint bounds are intermediate savings.
> The [factor-partition family](tseytin_universal_factor_partitions.md)
> independently reaches432/degree-at-most2012 from the frozen425 source.

The [literal source](tseytin_universal425.py) is a fixed universal integer
polynomial with **425=199M+226A operations**,405 certificate gates,
seven comparisons,65 positive witnesses, one fixed positive program
parameter and ordinary positive input. Its total degree is at most5868.
For every computably enumerable positive set T, an enumerator effectively
determines a positive constant A_T such that

\[
 x\in T\iff\exists z_1,\ldots,z_{65}>0:
 F(x,A_T,z_1,\ldots,z_{65})=0\qquad(x>0).
\]

A separate-unit construction costs **427=199M+228A**, degree at most5814,
with the same65 witnesses. The [receipt](tseytin_universal425.json)
contains all four complete schedules, including both SOS finalizers.
The overall75-certificate/87-polynomial record remains unchanged.

This improves the [complete440 baseline](tseytin_universal440.md) in
three separately justified steps:

1. [Selector and affine-offset sharing](tseytin_selector_sharing428.md)
   saves12 additions, with exactly the same integer polynomial and
   coordinates. The encoded-word predicate becomes362 operations.
2. The [52-operation exponent component](pell_fixed_affine_exponent52.md)
   saves one addition using a new affine index and reversed auxiliary
   signs. It retains the required input/output and signed projections,
   with fresh positive witnesses.
3. Loading the history's initial endpoint directly removes its two paid
   gates. This requires the program rescaling and proof below.

Only the first step preserves every arbitrary supplied tuple and its
polynomial value. The final construction has the same accepted input
relation on the stated program slices; it does not claim an identical
polynomial or a coordinate bijection with440.

## 1. The direct initial-endpoint loader

The word-history component previously supplied a positive `word` and
computed

    c2_initial_product=8 word,
    c2_initial=c2_initial_product+6.                         (1)

This is the sentinel code of the input word followed by the history
delimiter. Supply `I=c2_initial` as a positive coordinate instead and
delete both rows. The remaining word graph reads exactly that same
initial register. Its other endpoint `4096 Ufinal+3145` is unchanged.
The former `word` coordinate occurs nowhere else in that graph, as the
literal source guard verifies.

Use the constants and program word S from the baseline:

    B=8^32=2^96, d=B²−1,
    A_old=d 8^17 enc8(S)+h6,
    N_old(Q)=A_old Q^6+h4 Q^4+h3 Q^3+h1 Q+h0.

The [query-loader theorem](tseytin_affine_power_query_loader.md) proves
`N_old(B^x)=d enc8(S phi(beta r_x beta))`. Choose the new positive
program parameter and fixed coefficients as

    A=8 A_old,
    h_i'=8 h_i for i=1,3,4,6,
    h_0'=8 h_0+6d.

The new paid comparison is

    N(Q)=A Q^6+h4' Q^4+h3' Q^3+h1' Q+h0'=d I.                (2)

The exact identity `N=8 N_old+6d` proves that at Q=B^x,

    I=8 enc8(S phi(beta r_x beta))+6.                        (3)

The fixed coefficient h0' is still negative, as are h1',h3',h4'. Thus
the same ten-gate reused-power Horner schedule emits(2), simply with
changed integer constants and the input coordinate I. The program
parameter is supplied once when fixing the enumerator. No variable-time
scaling of A, division, exponentiation or encoding is omitted from the
count. There is no separate arithmetic gate for(3): it is the conclusion
of the retained loader equality, not an unpaid computational instruction.

## 2. The exponent projection and the sign filter

The52-operation component computes

    r=48x, Q=r+delta, X=2Q, Y=s,

with twelve positive auxiliaries. Its six-factor product P has the proved
necessary signed projection

    P=+1 implies Q=B^x,
    P=−1 implies Q=B^x/16,                                 (4)

whenever P is an integer unit and all its supplied coordinates are
positive. Every positive x has a complete positive extension with P=1.
Its proof also supplies extensions on the negative branch, so that branch
cannot be dismissed without using the loader.

Let W be the seven-factor product in the remaining word graph. Let
R1,...,R5 be its unchanged ordinary residuals, and R6=N(Q)−dI.
The complete merged polynomial is

    F=WP(1+R1²+...+R6²)−1.                                 (5)

At a zero, integer arithmetic forces WP=1 and all six residuals zero.
Each factor of W and P is therefore an integer unit. Apply(4) now,
before any use of the complete word-history theorem.

On the valid program recipe, `A=8h6 mod d`. If Q=B^x/16, the baseline's
exact two-parity sign certificate gives residues

    R_even=15759360 B+558888960,
    R_odd =24115200 B+550533120.

Since `N=8 N_old+6d`, the new numerator has residues `8 R_even` and
`8 R_odd`. Both are strictly between0 and d at B=2^96. Equivalently,
8 is invertible modulo d, so the baseline's nonzero residues cannot
become zero. Equation(2) requires residue zero and excludes this branch.
Thus **P=1, Q=B^x, W=1**. The receipt records both the original exact
cleared coefficient identities and the new residues, not just sampled
input values.

It would be premature to invoke the word theorem on an arbitrary positive
I, which need not be a valid delimited input code. Before this sign step,
the word block is used only as a product of integer factors and ordinary
integer residuals. Its semantic input is recovered only next.

## 3. Both universal directions and all positive coordinates

On a positive zero of(5), Section2 proves Q=B^x, so(2) implies(3).
Define the restored parent input mathematically by

    word=enc8(S phi(beta r_x beta))=(I−6)/8.

This is a positive integer by the literal query formula. Recomputing the
two deleted rows(1) gives the supplied I, and every other word-graph
register, factor and comparison matches its complete362-operation
parent. Since W=1 and R1,...,R5 vanish, that parent's theorem says
the actual query word equals `aaa` in the fixed C2 semigroup.

The complete440 proof supplies the effective program handoff: the
commutator recursive group detects T exactly, effective Higman embedding
gives a finite presentation with named a,b, and Tseytin's primary Lemma9
reduces `r_x=1` to this literal C2 equality. Hence x belongs to T.
Changing the query's numerical endpoint has changed none of those
group or semigroup hypotheses. No presentation-size bound is needed.

Conversely, let x belong to T. Choose the positive exponent52 extension,
the actual query word and any finite C2 derivation supplied by the primary
reduction. The complete word-history theorem gives all52 positive outer
and native coordinates for that derivation. Supply I by(3), which is
positive. The old and new word graphs now agree; the paid query equation
holds by its polynomial identity. Both products are1 and all residuals
vanish, so(5) is zero. There are exactly **52+12+1=65** positive
existential coordinates. All exponent coordinates are prefixed `exp__`,
so the two native constructions have no accidental shared auxiliary.

This is a mathematical positive extension theorem. The external effective
group embedding and full giant Pell tuples are not implemented or
numerically materialized in the receipt. The fixed C2 presentation and
all arithmetic source rows are literal and fully emitted.

The separate-unit form

    F_sep=W(1+R1²+...+R6²+(P−1)²)−1                         (6)

has the same universal property. Its zero first forces P=1 directly,
and then the same endpoint restoration proves soundness. Its converse
uses the same positive coordinates.

## 4. Complete count and degree

The shared word source has345 certificate gates. Deleting(1) leaves343.
The exponent has51 certificate gates and the fused loader still has10.
Thus the separate certificate costs404 gates with8 comparisons; its
23-gate finalizer yields427. Merging adds one multiplication and removes
one comparison, yielding405 certificate gates and a20-gate finalizer.

| Form | Certificate | Comparisons | Witnesses | Polynomial | M | A | Degree bound |
|---|---:|---:|---:|---:|---:|---:|---:|
|Merged product|405|7|65|425|199|226|5868|
|Separate product|404|8|65|427|199|228|5814|
|Merged SOS|405|7|65|425|199|226|11460|
|Separate SOS|404|8|65|427|199|228|11352|

All counts include operations on fixed numerals. The source checks that
every gate reaches its output and every supplied coordinate is declared.
Replacing the computed `8 word+6` by a supplied I retains its degree1.
Every retained word-source propagated degree is unchanged. Its main-norm
cancellation graph is unchanged too. The six exponent factor degrees
remain5,7,14,22,3,3 with sum54; the word factor bounds sum5676.
The maximum ordinary residual degree is still69, exceeding the fused
query degree7. Hence the merged bound is `5676+54+2*69=5868`, and the
separate bound is `5676+2*max(69,54)=5814`. Both cancellations are
identities at arbitrary supplied values. No zero-set relation is used
to reduce a formal degree, and exact expanded universal degree is not
claimed.

## 5. Reproducible checks and the nonidentity of final polynomials

`build(merge_units=True)` emits the default. The source and degree APIs
require the full canonical packet, including its program recipe,
comparisons, interfaces and positive coordinates. The initial-endpoint
rewrite checks the two exact deleted rows and their private input uses.
The remaining operand graph is topologically sorted and checked.

For a useful all-integer comparison, start with an arbitrary old word w
and old program A0, and set `I=8w+6`, `A=8A0`, retaining the new52-operation
exponent coordinates. Every word-graph register after(1) agrees, while
the new loader residual is eight times the old one, denoted q. If an
unfused intermediate uses those same new exponent coordinates, then

    F_fused−F_unfused=63 WP q²                   (merged product),
    F_fused−F_unfused=63 W q²                    (separate product),
    F_fused−F_unfused=63 q²                      (either SOS).   (7)

These identities explain exactly why endpoint fusion is not a whole
polynomial identity. They also avoid comparing the new52 exponent tuple
with the changed53 exponent semantics. The mathematical converse in
Section3, rather than an arbitrary-coordinate inverse, supplies the
required positive-zero equivalence on program/input slices.

The author receipt checks512 complete parent-register/manual-finalizer
identities on128 assignments, half signed. A separate96 affine endpoint
lifts give384 complete corrections(7), half signed. It checks96 literal
program/input queries and their excluded negative power branches, all
four ledgers/degrees/liveness graphs, and ten rejected mutated callers.
Loader fixtures use placeholder other auxiliaries and are not claimed
to be full Pell zeros. Run `python tseytin_universal425.py` for a fresh
receipt comparison; `--write` regenerates it. Author generation and a
separate fresh replay passed. Independent full proof/source/dependency
review and fresh replay passed without findings. Its separate executor
checks384 complete manual thirteen-factor/query/finalizer identities,
including192 signed cases, and256 exact endpoint-lift/finalizer
corrections, including128 signed cases. It also checks12 zero-selector
assignments, all four complete degree/opcode/closure audits and24 further
canonical guard rejections, and derives the fused negative residues from
the closed coefficient formulas.

A second independent review checks the endpoint/domain proof order and
effective one-parameter universality, both stripped-word graph and degree
restrictions, all four full degree/liveness/operation audits with both
norm cancellations, and24 additional literal endpoint/negative-branch
cases. All six local links resolve. Neither review claims an arbitrary
positive-I inverse or a materialized full giant Pell tuple.
