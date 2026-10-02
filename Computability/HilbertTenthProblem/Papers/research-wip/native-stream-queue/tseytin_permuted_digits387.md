# A digit permutation gives 387 universal polynomial operations

The [complete source](tseytin_permuted_digits387.py) recompiles the
[zero-a388 construction](tseytin_zero_a388.md) with digits

    a=0, b=3, c=1, d=2, e=4, #=5.

This saves one multiplication: **387=179M+208A**, with373 certificate
gates, five comparisons,62 positive witnesses, one fixed positive program
parameter A and ordinary positive input x. The total degree bound remains
**4712**. The separate-power form costs389, with bound4752. Their SOS
forms have the same respective operation counts and bounds9396 and9288.
The [receipt](tseytin_permuted_digits387.json) contains all four full sources.

For every computably enumerable positive set T there is an effectively
computed positive program numeral A_T such that, for x>0,

    x belongs to T iff there exist z1,...,z62>0 with F(x,A_T,z)=0.

The primary program word and C2 presentation retain their meaning. Program
numerals, copy indices and encoded histories change. The claim is equality
of accepted-input projections on the corresponding recompiled valid
program slices, not equality of polynomials or positive zero sets on the
same coordinate tuple. The separate75-certificate/87-polynomial results
are unchanged. No optimum over encodings or general arithmetic circuits
is asserted.

## 1. Literal encoding and the actual affine maps

Use enc(v)=8^|v|+raw8(v), with the six distinct digits displayed above.
A leading sentinel1 makes this injective, including words beginning or
ending in a=0. Every sentinel code is positive. The delimiter # remains
an actual symbol distinct from all five letters.

Order the copy tiles as #,e,b,d,c,a, so their offsets are5,4,3,2,1,0.
Leave the18 oriented relation tiles at indices6 through23. The literal
[presentation and word-history theorem](tseytin_c2_word_history.md) are
unchanged. Copy indices are relabeled by their symbols; no relation or
computation is added. All copy slopes are8, so every selected slope class
and its paid selector sum retains the same index set. The eight nonbaseline
classes, baseline64,24 selectors and top exponent34 are unchanged.

Each tile(l,r) acts by

    (U,V) -> (8^|l| U+raw8(l), 8^|r| V+raw8(r)).       (1)

All offsets are nonnegative and every slope plus offset is below65536.
For the noncopy relation pairs, the common minimum offsets are

    1,2,11,19,12,20,648,0,0,

where the final two zero minima belong to caaa/aaa and daaa/aaa and
share no paid offset subtotal. The unchanged literal word equation is

    top(selection) # aaa = query # bottom(selection).

The endpoint numerals are still

    I=8*enc(query)+5,   Vfinal=4096*Ufinal+2560,       (2)

since a=0 and #=5 retain raw8('#aaa')=2560. Both terminal operations stay
paid. Injectivity converts this integer endpoint equation back into the
literal string equation, whose splitting at # recovers C2 derivations.

## 2. The exact one-gate saving

Write h_i=Shat_i, the supplied selector hats. The copy offsets are in the
same descending numerical order as388, so the four-addition expression

    5h0+4h1+3h2+2h3+h4
      =h0+selector_sum__4+selector_sum__5
           +selector_sum__6+selector_sum__7

is unchanged. The first common paired offset is now1. Its paid product
`linear_coefficient__363=2*linear_group__362` is replaced by the already
paid group itself, saving one multiplication.

The four commuting relations ac/ca, ad/da, bc/cb and bd/db have correction
magnitudes7,14,14,7. With their literal orientations, the two contributions
are exactly

    upper: 7(h7+h12)+14(h9+h10),
    lower: 7(h6+h13)+14(h8+h11).                    (3)

For each side this uses two pair additions, two products and two additions
to the existing slope subtotal. The parent used one pair addition, three
products and three subtotal additions. Thus each side saves one
multiplication and preserves its number of additions.

Rows `linear_coefficient__396` and415 become the second pair sums in(3).
The now-private accumulator rows404 and423 disappear; their consumers
read403 and422. A fresh topological sort places the reused pair-sum rows
before their new consumers. Both identities hold on arbitrary integer
hats, without assuming selectors are one-hot.

The eca/ce and edb/de corrections become252 and255. Their paid groups
still give

    252h14+255h16=255(h14+h16)−3h14,
    252h15+255h17=255(h15+h17)−3h15.                (4)

Relative to388, the two new products3h14 and3h15 cost two multiplications.
The remaining correction magnitudes become4540,512,1024. The total raw
offset in either full coordinate is8066; the unchanged slope-hat correction
is37128, giving the shared subtraction45194. No additional term is hidden
in the hat convention. Both complete emitted updates equal

    N_U=64H_U+sum_j(a_j−64)(ZUhat_j−1)
                 +sum_i raw8(left_i)(Shat_i−1),
    N_V=64H_V+sum_j(b_j−64)(ZVhat_j−1)
                 +sum_i raw8(right_i)(Shat_i−1).    (5)

The ledger change is−1M from the common offset,−2M from(3), and+2M
from(4): **−1M overall, no change in A**. Three old rows disappear and
two new rows are inserted. No witness or comparison is removed.

## 3. The paid query and its sign filter

The literal suffix from the
[affine query loader](tseytin_affine_power_query_loader.md) is

    a (ab^63)^x abb (ab^31)^x abb
      (ab^63)^x abbb (ab^31)^x abbb aa.

It uses only a,b. Relative to388, a remains0 and b changes from1 to3.
Consequently its entire raw affine offset triples, while its slope remains
8^17 Q^6, where Q=8^(32x). Put d=8^64−1 and let h_j be the unfused388
tail coefficients. The new coefficients are exactly

    h'_j=3h_j,   h'_2=h'_5=0.                      (6)

They remain integral; h'_6>0 and the four lower fused coefficients stay
negative and nonzero. For the same valid primary program word S, now
encoded using c=1,d=2, set

    A=8*(d*8^17*enc(S)+h'_6)>0.                    (7)

This is an effective single positive program numeral. The paid loader is

    dI=A Q^6+8 sum_(j=0,1,3,4) h'_j Q^j+5d.        (8)

It still has ten gates. Neither the supplied input x nor the exponent52
subgraph is changed. In particular the exponent's signed-unit theorem
still gives Q=2^(96x) or Q=2^(96x−4) before the sign is selected.

Modulo d, the new program coefficient equals three times the corresponding
old coefficient: both program-encoding terms are multiples of d. The new
fused tail polynomial is three times the old one minus10d. Thus the two
wrong-power numerator residues are three times the388 residues, namely

    29966043244819123951156626953424814080,
    45854471631935696494459945720637767680.

Both are strictly between0 and d. The paid comparison(8) therefore excludes
the negative exponent-product branch on the recompiled valid program
slices. The exponent product is+1, and(8) recovers the exact first endpoint
in(2). This argument does not assert soundness for arbitrary positive A.

## 4. Direct soundness and positive completeness

The primary program S contains only c,d, both still nonzero. The explicit
suffix contains no aaa for x>0. Every binary zero run in the query followed
by # crosses at most two zero base-eight digits. Nonzero digits have at
most two leading and two trailing zero bits. Hence the exact initial I
has no binary zero run longer than10. The retained16-bit gap suffices.

Before any history interpretation, the native proof is unchanged from
[computed-field401](tseytin_computed_fields401.md) and388. Its inputs use
only the positive global bound, selector/range regions, q=16B P^34 and
reserved top tags2,1. Neither affine offset nor query numeral is used in
those pretyping inequalities. In particular they hold at D=1. The native
local sign/rank proof, after the query sign filter just established,
recovers dyadic B=65536D, P=B^t and the exact joined lower AND. It yields
one selected tile per physical row, selected slope products and current
history digits below D.

The lower transport reduces to I mod B<D. The
[free-height415 zero-run lemma](tseytin_free_height415.md), with16>10,
forces I<D. The upper transport gives initial digit1 and excludes D=1 at
this later stage. For a current digit u<D and any actual tile with
slope a>0 and offset c>=0,

    au+c < (a+c)D < 65536D=B.

Thus the update words in(5) have all physical digits below B and are
below P. The two exact transports recover terminal digits below B and
all chronological updates, without assuming a terminal height bound.
Equations(1)–(2) then give the literal accepting word equation and its
C2 derivation. This proves soundness for every positive new zero on a
valid recompiled program slice.

Conversely, take a genuine finite accepting C2 derivation. Relabel each
copy by its symbol in the new order and leave relation indices fixed.
Encode each concatenation with the new digits. All sentinel states stay
positive. Choose a sufficiently large dyadic D, then construct the
positive selector/product hats, repunit and global slack as in388.
Equations(5), both transports, the endpoint relation and the lower AND
hold for these actual histories. The unchanged native converse supplies
fresh positive private witnesses and its positive factored-bound gap.
The exponent52 converse and(7) supply the query component. This gives
a full positive387 extension.

A new zero therefore yields an actual accepting derivation, which may be
re-encoded to give a388 extension under its old recipe. Both directions
allow rebuilt histories and private witnesses. No coordinatewise inverse,
complete-polynomial identity with388, or preservation of an old program
numeral is claimed.

## 5. Guards, degrees and replay evidence

The rewrite requires equality to the entire canonical388 packet. It also
checks the literal private selector rows and the consumer sets for each
erased value. Active metadata is rebuilt from a whitelist. The new digits,
copy order and program recipe are explicit; historical parent narratives
remain inside the nested parent only. All complete-source and degree APIs
reject modified packets.

Every surviving propagated degree equals its parent bound, and the two
new numeral products have degree1. The two exact native/exponent main-norm
cancellation subgraphs remain literal and unchanged. A guarded generic
propagation checks the full degree dictionary and all four finalizers.
These are degree upper bounds, not exact expanded-degree assertions.

The receipt checks384 complete modified-parent/manual-finalizer outputs
(192 signed),384 complete updates against all24 actual maps and192 retained
nonupdate-register maps(96 signed), including12 zero-selector contexts.
The parent replay explicitly overrides whole affine updates and the query
coefficients; it never asserts equality with the unchanged old polynomial.
It also checks96 literal paid queries, both wrong-power residues,9331
injective sentinel encodings and72 contextual rewrites. Independently
assembled accepting paths are packed into the actual outer source to
check global and transport comparisons, update words and the joined AND.
These are source, query and outer-history fixtures, not complete native
Pell-zero tuples. The receipt records their exact counts and all emitted
sources. Default execution replays it; `--write` regenerates it.

Author writer72553 and fresh replay20339 passed. Root independently
read the full proof, source and dependencies and passed fresh27921,
with no findings. Its separate audit checked192 modified-definition
register maps(96 signed),384 complete modified-parent/manual-finalizer
outputs(192 signed),384 literal tile updates,16 zero-selector cases,
four independently propagated degree/domain/opcode/closure ledgers,24
malformed callers,72 literal-query closed forms and both wrong-power
residues. It independently packed63 accepting histories(60 with delimiter
copies),901 steps: all global/transport comparisons and joined AND passed.
Seven local links and whitespace passed; none of these fixtures is a full
native Pell zero. Source scope is this explicit digit permutation and schedule;
no finite permutation search or general optimality claim is part of it.
