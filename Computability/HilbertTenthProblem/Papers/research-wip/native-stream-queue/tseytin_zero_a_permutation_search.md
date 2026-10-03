# Exact digit-permutation search in one paid C2 affine architecture

Among the120 permutations considered here, the minimum is
**387=179M+208A**. Sixteen permutations attain it, including the explicit
[387 compiler](tseytin_permuted_digits387.md). This is an exact minimum
inside the affine-update architecture defined below. It is not a lower
bound over other arithmetic circuits, letter encodings, radices or
universal substrates.

The [source](tseytin_zero_a_permutation_search.py) emits a complete
universal polynomial for every permutation. Each has one fixed positive
program parameter A, ordinary positive input x and62 positive witnesses.
The merged minimum uses373 certificate operations and five comparisons,
with propagated degree bound4712. The separate-power form costs389;
the same-cost SOS options and their bounds are recorded individually.
The [receipt](tseytin_zero_a_permutation_search.json) contains all480
ledgers and the four complete default schedules. The independent
75-certificate/87-polynomial operation bounds are unchanged.

## 1. The finite architecture and valid encodings

Start with the full [zero-a388 source](tseytin_zero_a388.md). Fix digit
(a)=0 and assign the other five symbols b,c,d,e,# bijectively to1,...,5.
Order the six copy tiles in decreasing digit order. Keep the eighteen
oriented relation tiles at indices6,...,23, in the same order:

    ac=ca, ad=da, bc=cb, bd=db, eca=ce, edb=de,
    cdca=cdcae, caaa=aaa, daaa=aaa.

Each displayed relation contributes its forward and reverse tile. The
encoding is enc(v)=8^|v|+raw8(v), including the leading sentinel1.
It is injective even with leading or trailing a symbols. Every copy
has slope8. Reordering copies therefore preserves all existing slope
classes and selector-product groupings. The symbolic word system is
unchanged.

The following choices, and only these choices, are optimized:

1. Compute the copy-offset form from already-paid selector prefixes in
   descending digit order.
2. For each oriented relation pair, share its minimum raw offset between
   the two coordinate updates. Omit a zero minimum.
3. In the four commutation pairs, group exactly the correction selectors
   with equal positive difference magnitude.
4. For eca/ce and edb/de, choose direct terms or the decomposition through
   the already-paid selectors14+16 and15+17, whichever is cheaper.
5. Omit multiplication by1. Charge every other numerical multiplication,
   subtotal addition, subtraction and accumulation into the update.

The three remaining nonzero difference terms in each coordinate are
emitted directly. The fixed history/native/exponent graph, paid input
loader architecture and finalizers are retained. Cross-stage algebraic
factoring, different common-offset choices and other weighted linear
circuits are outside this finite objective.

The checker validates the complete canonical388 parent before replacing
its linear update kernel. It checks that the only external consumers of
that kernel are its five required selector-pair subtotals and two update
ports. The resulting complete source is topologically checked and every
gate reaches the final output. Old historical metadata is not promoted:
the new packet explicitly records its digits, ordered tiles, program
recipe and accepted-input scope.

## 2. Literal affine forms and exact operation count

Write b,c,d,e,z for the five positive digit values, with z the delimiter.
The first four commutation difference magnitudes are

    7c, 7d, 7|b−c|, 7|b−d|.

Let

    G = number of distinct values among c,d,|b−c|,|b−d|,
    t = 1 if c=1 or d=1, and0 otherwise,
    j = 2 if b=1, and4 otherwise.                   (1)

These are numerical facts about one fixed encoding, not runtime inputs.
The seven positive common minima are

    c, d, min(8b+c,8c+b), min(8b+d,8d+b),
    8c+e, 8d+e, 520c+64d.                          (2)

The final two pair minima are zero because raw8(aaa)=0. Only c or d
can make a positive minimum equal one, and at most one does so.

Put h_i=Shat_i. Since the copy digits descend from5 to0, their shared
weighted form is

    5h0+4h1+3h2+2h3+h4
      =h0+(h0+h1)+(h0+h1+h2)
           +(h0+h1+h2+h3)+(h0+h1+h2+h3+h4).        (3)

All four parenthesized prefixes are already paid by the retained source.
Four new additions combine them. For each coordinate, grouping the
four commutation corrections uses4−G subtotal additions, G numerical
multiplications and G accumulations. Its cost is therefore G M+4 A.
The selected high-offset tile is obtained from its actual orientation;
it is not assumed to have the old numeric index parity.

The next two differences are63e and63e+b. In the upper coordinate,

    63e*h14+(63e+b)*h16
      =(63e+b)*(h14+h16)−b*h14,                    (4)

and the lower coordinate uses h15,h17. The parent already computes both
pair sums. If b=1, each expression costs one multiplication and one
subtraction, then one accumulation into the update. Otherwise it costs
two multiplications and those two additions/subtractions, tying the
direct form. Across both coordinates this gives j M+4 A.
The three remaining differences are

    3640c+448d+e, 512c, 512d,

all greater than one; they cost6 M+6 A across both coordinates.

The following table charges the whole replaceable kernel, including
subtotals which also feed the retained selector sum:

|Component|M|A|
|---|---:|---:|
|Two five-term slope forms|10|8|
|Seven shared pair subtotals|0|7|
|Copy form(3)|0|4|
|Seven positive minima and their accumulations|7−t|7|
|Shared hat-offset subtraction|0|1|
|Four commutation corrections in both coordinates|2G|8|
|Two adjacent differences in both coordinates|j|4|
|Three remaining differences in both coordinates|6|6|
|Add the common form to both updates|0|2|
|Total|23+2G+j−t|47|

The fixed remainder of the merged polynomial costs149 M+161 A.
Consequently the complete source has

    M=172+2G+j−t, A=208,
    operations=380+2G+j−t.                         (5)

Separating the word and exponent products adds two additions, as in the
parent. Both finalizer choices retain the corresponding operation count.
The receipt checks(5) against every emitted schedule, rather than
charging a symbolic abbreviation as a free gate.

For clarity, the emitted update in coordinate side is exactly

    64*H_side
      +sum_k slope_difference_k*(Zsidehat_k−1)
      +sum_i raw8(tile_side_i)*(Shat_i−1).          (6)

The slope differences are −56,448,4032,32704, with the last two reversed
on the lower side. Their sum is37128. The shared subtracted constant is
37128 plus the sum of all24 raw offsets in either coordinate; those two
raw sums agree because every relation occurs in both orientations.
An independent sparse coefficient executor checks(6) as an exact linear
polynomial in all supplied ports for all120 encodings. Thus the identity
holds on arbitrary signed assignments, not only typed selectors.

## 3. Finite optimum and all minimizers

Since c and d are distinct, G>=2. If b=1, neither c nor d is1, so t=0.
Moreover min(c,d)−1 is another positive magnitude strictly smaller than
both c and d, giving G>=3. Equation(5) then gives at least388.
If b is not1, j=4 and t<=1, so(5) gives at least387.

The lower bound387 is attained exactly when G=2 and t=1 in the latter
case. The16 minimizers are compactly listed below: c,d may be exchanged,
and e,# may independently be exchanged in each row.

|b|{c,d}|{e,#}|Number of assignments|
|---:|---|---|---:|
|2|{1,3}|{4,5}|4|
|3|{1,2}|{4,5}|4|
|4|{1,3}|{2,5}|4|
|5|{1,4}|{2,3}|4|

The receipt lists every one individually. The exact distribution over
all120 permutations is

|Operations|Number of permutations|
|---:|---:|
|387|16|
|388|16|
|389|24|
|390|36|
|391|8|
|392|20|

The default is (a,b,c,d,e,#)=(0,3,1,2,4,5), with copies #,e,b,d,c,a.
Its common minima are1,2,11,19,12,20,648; its shared hat subtraction is
45194. This emitter and the independently authored387 source use the
same literal maps and program recipe. Equation(6), the unchanged graph
outside the guarded boundary, and the same loader coefficients establish
their complete polynomial identity. The checker also executes both full
sources on signed assignments; it does not assume identical expression
trees or rely on an equality valid only at solutions.

## 4. Every enumerated encoding retains the universal interface

Let d0=8^64−1 and let h_i be the exact unfused suffix coefficients of
zero-a388. The literal variable suffix uses only a and b, so replacing
b=1 by b=k multiplies every h_i by k. Its two zero coefficients remain
zero. For the inherited valid primary literal program word S over c,d,
recompile the single positive program numeral as

    A=8*(d0*8^17*enc_codes(S)+k*h6).                (7)

The positive sentinel and h6>0 make A positive. The complete paid loader
is still ten gates and asserts

    d0*I=A*Q^6+8k*sum_(i=0,1,3,4) h_i*Q^i+z*d0.    (8)

No exponent or query-word construction is treated as free. The fixed
exponent52 source is retained unchanged. At a unit zero it has the two
possible signed branches Q=2^(96x) or Q=2^(96x−4). On the valid recipe(7),
the latter branch gives, according to the parity of x, the residues kR1
or kR2 modulo d0, where

    R1=9988681081606374650385542317808271360,
    R2=15284823877311898831486648573545922560.

The zero-a388 coefficient proof gives these R values; the new numerator
is k times that numerator modulo d0 because its delimiter term is a
multiple of d0. The exact inequalities0<kR_i<=5R_i<d0 exclude both wrong
branches. This occurs before word semantics or initial-height recovery.
Thus the exponent product is+1, Q=8^(32x), and(8) forces the exact recoded
endpoint I=enc_codes(query #).

All codes for c,d,# are nonzero, so the valid program word S has no zero
symbol. The literal query suffix has no run of three a's for positive x.
A nonzero three-bit digit has at most two leading and two trailing zero
bits. Any binary zero run in I therefore has length at most

    2+2*3+2=10<16.                                 (9)

The native field/rank/scale proof and scalar pretyping ports are
unchanged by the affine coefficients. As in the parent, the paid lower
transport first gives I modulo B<D; only after the loader and(9) may
the sixteen-bit endpoint lemma give I<D. Every actual map has
nonnegative offset and slope plus offset below65536. Hence the same
chronological transports recover real current, next and terminal states
with no carry. The sentinel encoding yields the unchanged literal
word equation, and the C2 derivation theorem gives soundness.

For completeness, take the finite literal derivation of an accepted
input, reorder each copy index and encode its words with the chosen
digits. Choose a sufficiently large dyadic height and rebuild the
packed history, selected-product hats and private native witnesses.
The parent completeness proof applies to the same slope classes and
margins; the exponent converse and(7)–(8) complete the input loader.
Thus every enumerated encoding is universal on its recompiled valid
program slices. This does not assert that an arbitrary literal S over
c,d is a valid primary program, or that arbitrary positive A is valid.
Nor does it give a coordinatewise positive-zero bijection between
encodings: history numbers, heights and native witnesses can change.

## 5. API, degree bounds and evidence

`build(digits, merge_units=True|False)` returns a fresh full canonical
packet. Digits must be exactly the specified integer bijection; booleans,
floats, omitted symbols and duplicate values are rejected.
`polynomial_source(packet, sum_of_squares=True|False)` emits the complete
schedule. Full packet equality guards all public finalizer/degree APIs,
including domains, interfaces, codes, tile order and program recipe.
`program_parameter(S,digits)` implements(7); its arithmetic domain is
literal words over c,d, with semantic validity supplied by the inherited
primary-program construction.

The new kernel is linear in the same ports, all changed coefficients
are fixed numerals, and the two guarded native/exponent norm cancellations
are unchanged. Literal degree propagation gives the parent's respective
bounds: merged4712, separate4752, merged SOS9396, separate SOS9288.
These are propagated bounds, not claims about exact expanded universal
degree or an optimized degree frontier.

The deterministic audit enumerates all120 cases and checks240 exact
symbolic affine identities,480 complete opcode/liveness/degree ledgers,
1,920 whole modified-parent output identities(960 signed),1,800 literal
query/zero-run instances and240 exact wrong-power residues. The parent
oracle changes only the two literal update ports and the paid loader/
terminal constants; it does not claim equality to the old encoding.
A separate256 full-output comparison with the actual387 source includes
128 signed cases. Four complete default sources and their hashes are
stored in the receipt. These are finite source/word fixtures, not complete
native Pell-zero tuples. Writer63596 and a separate author fresh
replay95603 passed on the same source and receipt. Twenty-two
malformed callers are rejected; all four local destinations and whitespace
checks pass.

Franklin independently read the complete proof, source and dependencies
and passed fresh replay87157 with no findings. His separate oracle rebuilt
240 exact affine forms from literal source ancestry, checked480 complete
opcode/liveness/degree ledgers,960 manual-boundary complete outputs
(480 signed),720 new literal-query/zero-run cases,240 exact wrong-power
residues, the full distribution and all16 minimizers. It also checked
canonical metadata, positive program recompilation, loader-before-height
ordering and the architecture-only optimum scope. Four links passed.

Root independently read the complete proof and source and passed fresh
replay53757 without findings. A further independent basis executor checked
8,400 affine constant/basis identities across all120 kernels,480 literal
opcode ledgers,720 independently concatenated queries and240 residues
computed from closed coefficients, reproducing the same distribution.
The final batch audit verifies all emitted source hashes and local links.
These audits supplement the symbolic proof; no complete enormous native
Pell zero is claimed.
