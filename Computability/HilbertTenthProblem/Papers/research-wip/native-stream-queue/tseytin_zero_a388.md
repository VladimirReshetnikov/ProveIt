# Zero a and reversed copies give388 universal polynomial operations

The [source](tseytin_zero_a388.py) changes the six digit codes and the
order of the copy tiles in the [paid-prefix395 compiler](tseytin_copy_prefix395.md).
It reaches **388=180M+208A**,374 certificate gates, five comparisons,
62 positive witnesses, one fixed positive program parameter A and
ordinary positive input x. Its total degree is **at most4712**.
The separate-power form costs390 with bound4752. The corresponding
SOS bounds are9396 and9288, respectively, at the same respective costs.
The [receipt](tseytin_zero_a388.json) contains all four complete sources.

The universal theorem is, for every computably enumerable positive set T,

    x in T iff there exist z1,...,z62>0 with F(x,A_T,z)=0,  x>0.

The effective program recipe A_T is recompiled below. The actual C2
presentation and its24 physical tiles remain the computational substrate.
Only their numeric encoding and six copy indices change. This saves
seven gates from395 and six from the independently established
[zero-delimiter394 alternative](tseytin_zero_delimiter394.md).
The separate75-certificate/87-polynomial compiler bounds are unchanged.

The equivalence is between existential accepted-input projections on the
corresponding valid program slices. No same-coordinate polynomial identity
or positive-zero bijection with an earlier encoding is claimed. Both
histories and private native witnesses may change under recoding.

## 1. Literal word system, zero digit and reversed copy order

Assign

    a=0, b=1, c=2, d=3, e=4, #=5.

For a word v define enc(v)=8^|v|+raw8(v). Its base-eight expansion is a
leading sentinel1 followed by its exact digit string. This is injective
for all finite words, including words with initial or terminal a's. A
zero a digit remains a symbol, not an empty word; # remains distinct.
All sentinel encodings are positive.

Order the first six copy tiles as #,e,d,c,b,a. Keep the18 oriented
relation tiles at their former indices6 through23. The source exposes
this entire new tile list. Each tile(l,r) still acts by

    (U,V) -> (8^|l| U+raw8(l), 8^|r| V+raw8(r)).

Every copy slope is8, so reversing their indices leaves every paid slope
class and selected-product grouping unchanged. The relation words and
slope groups are unchanged too. All offsets are nonnegative, and every
slope plus offset is less than65536; the same history radix margin applies.

The literal [word-history theorem](tseytin_c2_word_history.md) uses only
the string equation

    top(selection) # aaa = query # bottom(selection).

Its decomposition at the actual delimiter symbol is independent of digit
values. Its new boundary values are

    I=enc(query #)=8*enc(query)+5,
    Vfinal=4096*Ufinal+2560,                         (1)

since raw8('#aaa')=5000 in base8. Both operations at the terminal remain
paid. The endpoint Ufinal remains a supplied positive witness.

## 2. Seven eliminated operations and exact affine updates

Write h_i=Shat_i. The new copy offsets are5,4,3,2,1,0. Their weighted sum
is

    5h0+4h1+3h2+2h3+h4
       =h0+selector_sum__4+selector_sum__5
          +selector_sum__6+selector_sum__7.          (2)

Those prefixes were already paid: they contain h0+h1 through h0+...+h4.
Four additions now replace the parent's one multiplication and five
subtractions. Delete `linear0_coefficient__50` and `linear_sum__380`,
then reuse rows381 through384 for(2). This saves1M+1A.

All four oriented caaa/aaa and daaa/aaa tiles share the minimum offset
raw8('aaa')=0. Their private selector subtotal is no longer needed.
Delete `linear_group__376`,377,378, `linear_coefficient__379` and
`linear_sum__392`; the shared-offset row reads391 directly. This saves
another1M+4A. The all-selector sum uses a different already paid tree,
so no selector or native input is lost.

Recomputed common offsets for the eight paired groups are

    2,3,10,11,20,28,1232,0.

The first four correction magnitudes remain14,21,7,14, with their
original orientations. The eca/ce and edb/de differences are252 and253,
so the adjacent pair remains one253-times-paid-group minus one selector.
The remaining correction magnitudes become8628,1024,1536. The total
raw offset over all tiles is14376 in either coordinate; the unchanged
slope-hat correction is37128. Thus the shared subtraction is51504.
The complete new emitted updates are exactly

    64H_U + sum_j slope_difference_Uj*(ZUhat_j−1)
          + sum_i raw8(left_i)*(Shat_i−1),
    64H_V + sum_j slope_difference_Vj*(ZVhat_j−1)
          + sum_i raw8(right_i)*(Shat_i−1).            (3)

These are arbitrary-integer identities, not only identities for one-hot
selectors. They account for every changed coefficient and both hat
constant corrections. The total saving is2M+5A, with no new coordinate,
comparison or uncharged operation.

## 3. Sparse paid query and unchanged exclusion of the wrong power

Let d=8^64−1. The literal suffix from the
[affine query loader](tseytin_affine_power_query_loader.md) is unchanged:

    a (ab^63)^x abb (ab^31)^x abb
      (ab^63)^x abbb (ab^31)^x abbb aa.

Its length is192x+17. Concatenating its affine word maps over exact
rationals gives slope8^17 Q^6 and tail polynomial sum h'_j Q^j,
with Q=8^(32x), after multiplying the offsets by d. The source performs
this exact compilation. If h_j are the original unfused digit1..6
coefficients, shifting every digit down by1 gives

    h'_0=h_0+d/7, h'_6=h_6−d*8^17/7,
    h'_j=h_j for1<=j<=5; h'_2=h'_5=0.                (4)

For the original valid literal primary word S, now define

    A=8*(d*8^17*enc(S)+h'_6).                        (5)

This is a positive, effectively computable single program numeral.
Its leading sentinel term is positive and h'_6 is positive, as the
exact coefficient compilation verifies. The original program-word
construction and its meaning are retained; the old numeric A is not.
The paid query comparison is

    dI=A Q^6+8 sum_(j=0,1,3,4) h'_j Q^j+5d.         (6)

There are still ten arithmetic gates: the two zero coefficients remain
zero and the lower four fused coefficients remain nonzero. The existing
exponent52 source and its parameters are unchanged.

The [fused loader sign proof](tseytin_universal425.md) tests the two
possible wrong-power residues Q=(8^32)^e/16 modulo d, e=1 or2. The
change in the full fused numerator under the old/new program recipes is,
modulo d,

    (d/7)*(1−8^18 Q^6).

Here Q is a unit modulo7, Q^6=1 modulo7, and8^18=1 modulo7. The
expression is therefore a multiple of d. The original two nonzero
residues persist exactly:

    9988681081606374650385542317808271360,
    15284823877311898831486648573545922560.

Thus the wrong exponent-product sign is excluded before native typing.
The exponent product is+1 and(6) recovers the exact endpoint I in(1).
The residue claim is on the recompiled valid program slices, not for
arbitrary positive A.

## 4. The input-height proof survives zero a digits

The primary word S contains only c,d, both now nonzero digits. For x>0,
the displayed suffix has no three consecutive a's. All other digits in
the full query followed by # are nonzero. A nonzero three-bit base-eight
digit has at most two leading and two trailing binary zeros. A run
crossing one or two a digits therefore has length at most

    2+2*3+2=10.

The sentinel and terminal #=5 obey the same bound. Consequently I has
no binary zero run longer than10. This is the needed substitute for the
old positive-letter bound4: the retained sixteen-bit margin still wins.

The pretyping bounds and local sign/rank proof of the
[computed-field401 compiler](tseytin_computed_fields401.md) use only the
unchanged global positive bound, selector and range regions, q=16B P^34,
fixed top tags2 and1, and the native graph. They do not depend on the
affine update offsets, terminal constant or query code. They apply even
at D=1, and recover dyadic B=65536D, P=B^t and the exact lower
selector/range AND. The current history digits are below D.

The lower transport then gives I mod B<D. Since16>10, the zero-run
lemma from the [free-height415 proof](tseytin_free_height415.md) gives
I<D. The upper transport gives initial digit1, hence excludes D=1 only
at this later stage. Formula(3), with nonnegative offsets and slope plus
offset below65536, keeps every actual update below B. Both paid
transports therefore recover the genuine terminal digits below B and
all chronological updates. The extracted endpoints are(1); sentinel
injectivity yields the literal string equation. Splitting at # recovers
an accepting C2 derivation and hence the stated accepted ordinary input.

This order avoids assuming an input-height bound, one-hot selectors or
a valid word computation while deriving the native scalar bounds.

## 5. Positive completeness, guards, degrees and finite evidence

For an accepted input, choose its finite literal C2 derivation. Replace
copy index i<6 by5−i, leave every relation index fixed, and encode all
concatenations with the new digits. Choose a sufficiently large dyadic
height D for the finitely many positive sentinel states. The same
repunit construction supplies positive selector/product hats. The exact
updates(3), terminal(1), scalar margins and lower AND all hold. The
native converse supplies fresh positive private witnesses at q; its
canonical exponent makes the retained factored bound gap positive.
The exponent52 converse and(5)–(6) give the query component. This is a
complete positive388 extension.

Conversely the soundness just proved extracts an actual finite accepting
derivation from a positive388 zero. Re-encode that derivation and rebuild
sufficiently large histories and private native witnesses to obtain a
395 zero at the old recipe if desired. This is equality of existential
input projections on corresponding program slices, without a claimed
coordinatewise inverse on supplied zeros.

The rewrite requires the whole canonical395 packet, checks the exact
changed/private rows and their consumer sets, and preserves only active
scalar/compiler metadata. The new digit map, tile order and program
recipe are explicit. Old identity narratives stay in the nested parent.
Complete-source and degree APIs reject mutated packets. Every surviving
degree bound equals the parent's: changed constants have degree0,
selector sums degree1, and the two guarded norm cancellations are
unchanged. Exact expanded universal degree is not asserted.

The receipt checks256 full modified-definition outputs(128 signed),256
complete updates against all actual24 maps,96 literal paid queries,
both wrong-power residues,9331 injective sentinel codes,72 contextual
rewrites and four accepting append histories, including delimiter copies.
The parent replay explicitly overrides changed definitions; it does not
assert identity with the old polynomial. All four full sources pass
opcode counts and output closure. These are finite source/word fixtures,
not complete native Pell-zero tuples. Author generation3129 and fresh replay93728 passed.

Native independently read the complete proof, source and dependencies,
then passed fresh replay32945 without findings. His separate audit
checked192 complete modified-definition register maps(96 signed),384
modified-parent/manual-finalizer outputs(192 signed),384 literal tile
update identities,16 zero-selector cases, four complete degree/domain/
opcode/closure ledgers,24 malformed callers,72 literal query formulas
and both wrong-power residues. It independently packed63 accepting
histories(60 with delimiter copies),901 actual steps: every retained
global/transport comparison and joined AND passed. A separate concept
audit checked288 actual queries,75 zero-run boundaries including the
sharp generic eaab length10, and55,987 sentinel codes. Nine local links
and whitespace passed. None of these fixtures is a full native Pell zero.
