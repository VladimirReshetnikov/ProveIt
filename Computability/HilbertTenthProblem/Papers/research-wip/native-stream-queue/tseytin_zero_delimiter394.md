# A zero delimiter gives394 universal polynomial operations

> The later [digit-permutation construction](tseytin_permuted_digits387.md)
> reaches387 operations with62 witnesses and degree at most4712.
> It recompiles program numerals and histories. This note retains the
> distinct source and precise equivalence claim of its own stage.

The [source](tseytin_zero_delimiter394.py) changes the delimiter's digit
from6 to0 in the [paid-prefix395 compiler](tseytin_copy_prefix395.md).
It saves one addition, giving **394=182M+212A**,380 certificate gates,
five comparisons,62 positive witnesses, one fixed positive program
parameter, ordinary positive input, and degree **at most4712**.
The separate-power form costs396 and has degree bound4752. The
respective SOS bounds are9396 and9288, at the same respective operation
counts. The [receipt](tseytin_zero_delimiter394.json) emits all four sources.

The literal C2 presentation,24 physical tiles, letter codes1 through5,
program numeral and ordinary input are retained. Only the fresh delimiter
uses digit0. A zero symbol is permitted by the sentinel word encoding and
the affine history theorem. The input-height argument needs a separate
check, supplied below: the actual query ends inaa, so its appended zero
digit does not lengthen any binary zero run beyond the existing bound4.

The result preserves the accepted-input projection on the same valid
program slices. Histories are recoded and private native witnesses are
rebuilt. The parent and successor need not agree on the same numerical
witness tuple, and no complete-polynomial or positive-zero bijection to
395 is claimed. The separate75 certificate /87 polynomial operation
bounds remain unchanged.

## 1. The same word equation with a different delimiter digit

Let the six digits now be

    a=1, b=2, c=3, d=4, e=5, #=0.

For every word v over these six symbols define

    enc(v)=8^|v|+raw8(v).

Its canonical base-eight expansion has leading sentinel1 followed by
exactly the digit string v. All digits lie in[0,7], so this remains
injective, including words beginning or ending with #. Appending a
zero multiplies a positive sentinel code by8 and remains positive.
The symbol # is still distinct from every letter. Its zero digit is
not deletion of that symbol or the empty word.

Every tile still acts by

    (U,V) -> (8^|l| U+raw8(l), 8^|r| V+raw8(r)).

Only tile5, the delimiter copy, changes its affine map:

    (8,6,8,6) -> (8,0,8,0).                         (1)

The two slope sets, baseline64, eight selected slope-class products,
24 selectors and history exponent34 are unchanged. All offsets remain
nonnegative and every slope plus offset is below65536. The ordinary
integer and chronological estimates of the complete history therefore
remain valid after replacing the two tile5 offsets by0.

The same exact string equation still characterizes C2 derivability:

    top(selection) # aaa = query # bottom(selection).

Splitting at the actual symbol # recovers the succession of contextual
rewrites, exactly as in the [literal word-history proof](tseytin_c2_word_history.md).
This argument depends on injectivity and distinct delimiters, not on
a positive digit for every symbol. All sides of the nine actual defining
relations stay nonempty. The corresponding boundary values become

    I=enc(query #)=8*enc(query),
    Vfinal=enc(top # aaa)=4096*Ufinal+73,             (2)

because raw8('#aaa')=raw8('0111')=73. The multiplication by4096 and
addition of73 remain paid. Ufinal is still a supplied positive witness.

## 2. Exact shorter copy-offset arithmetic

The parent shares the weighted copy-selector sum

    h0+2h1+3h2+4h3+5h4+6h5,

where h_i=Shat_i. The new sum omits the delimiter term6h5. The already
paid selector prefixes give its exact expression

    h0+2h1+3h2+4h3+5h4
      =5*selector_sum__7−selector_sum__6
       −selector_sum__5−selector_sum__4−h0.         (3)

Thus the one multiplication remains, and one subtraction disappears.
Concretely `linear0_coefficient__50` becomes5*selector_sum__7;
`linear_sum__380` is deleted and its sole consumer reads this product
directly. The remaining four subtraction rows still end at
`linear_sum__384`. They are then used by both affine updates.

The source computes offsets on unhat selectors S_i=Shat_i−1. Accordingly,
the shared constant subtraction changes from58328 to58322: the two
updates each lose exactly6(Shat5−1), not6Shat5. An independent expansion
against all24 actual affine maps checks both entire update expressions.
No slope or selected-product coefficient changes.

## 3. Paid query, power-sign filter and input height

Use the same literal primary program word S and the same positive
program coefficient as the [fused425 query loader](tseytin_universal425.md).
Let d=8^64−1 and h_j be that loader's original *unfused* coefficients.
Its numerator N satisfies d*enc(query)=N at Q=8^(32x). The old fused
initial endpoint used8N+6d. The new one uses **8N**, so its final constant
is changed by subtracting another6d. Every other query row, coefficient,
comparison and supplied program/input parameter is unchanged. The
last coefficient remains nonzero and the ten-gate loader cost is retained.

For either input parity, the negative exponent-product branch gives the
same nonzero numerator residue modulo d as before: subtracting6d has
no effect. Thus the paid comparison still excludes that branch before
any history typing. The exponent product is+1 and the exact initial
value in(2) follows. This uses the actual unchanged program recipe;
no claim about unrestricted program coefficients is made.

All letters in the query have nonzero base-eight digits1 through5,
so their binary expansion has zero runs of length at most4. The explicit
query concatenation ends in the fixed suffixaa, with digit1 last.
Appending # adds exactly three trailing zero bits. It joins no previous
zero run, because the last bit of digit1 is1. Therefore the initial
value I in(2) still has **no binary zero run longer than4**, for every
positive x and every actual program word S.

The complete native scalar bounds and local sign/power proof of the
[computed-field401 compiler](tseytin_computed_fields401.md) use only the
unchanged global bound, selector/range regions, q=16B*P^34 and fixed
top tags2,1. They do not depend on the delimiter offset or any terminal
code. In particular they remain valid at D=1 before typing. They recover
dyadic B=65536D and P=B^t, and the same exact lower selector/range AND.
Its current digits are below D. Reducing the new lower transport modulo
B gives I mod B<D. Since16>4, the established zero-run lemma gives
I<D; the upper transport gives its initial digit1, excluding D=1 only
at this later stage. Every recoded affine update is still below B,
so the paid transports recover both terminal digits below B and exact
chronology, as in the [free-height415 proof](tseytin_free_height415.md).

The recovered endpoints are precisely(2). Sentinel injectivity turns
them into the unchanged word equation. Splitting it at # gives the
literal C2 derivation and the same accepted ordinary input.

## 4. Positive completeness and the preservation claim

For an accepted input, take its genuine finite C2 derivation and the
same delimiter-copy tile sequence. Recode each concatenation using
#=0, retaining the same actual letters and contextual rewrites.
Every sentinel value remains positive. Choose a sufficiently large
dyadic height D for the finitely many current states, and construct
the positive selector/product hats and exact history repunit as usual.
The recoded maps satisfy all unchanged scalar margins and the new
terminal relation4096Ufinal+73. Their lower AND lanes are genuine;
the prescribed native converse supplies positive private witnesses at
the resulting q. Its canonical exponent makes the factored bound gap
positive. The unchanged exponent52 converse supplies the query component,
whose numerator now enforces the first relation in(2). Hence every
accepted input has a positive new extension.

Conversely Section3 extracts an actual accepting derivation from any
positive new zero on a valid program slice. Re-encoding that finite
derivation with the old delimiter6 and rebuilding a sufficiently large
positive parent history gives a395 extension if desired. This establishes
equality of existential input projections; numerical histories and native
witnesses can change in either direction. Neither an affine code conversion
on arbitrary integers nor a positive coordinate bijection is presumed.

## 5. Guards, degrees and finite evidence

The guard requires the entire canonical395 parent and checks the literal
prefix, update-offset, endpoint and query rows, plus the deleted row's
only consumer. Active metadata is rebuilt from an explicit whitelist;
historical identity claims stay in the nested parent record. The active
projection explicitly states #=0 and I=8*enc(query). The source/output/
degree APIs reject altered successor arithmetic, recipe or interfaces.

Every surviving register retains its former degree bound. The changed
fixed constants have degree zero, the shorter copy expression is nonzero
of degree1, and both native/exponent main-norm cancellation subgraphs are
unchanged. A fresh generic guarded degree propagation agrees with the
entire retained395 dictionary. Thus all four degree bounds are unchanged;
exact expanded universal degrees are not asserted.

The receipt contains256 full modified-parent output identities(128 signed)
and256 complete affine-update identities against the actual recoded24
maps. The parent replay explicitly overrides the changed definitions;
it is not evidence that the unmodified old polynomial is identical.
It also checks96 literal paid queries, both exact wrong-power residues,
9331 injective sentinel encodings,72 contextual rewrites and four genuine
accepting append histories, two containing delimiter copies. These are
word, scalar and source fixtures, not full native Pell-zero tuples.
All four complete sources have output closure. Default execution replays
the receipt; `--write` regenerates it. Author generation and fresh replay passed. Native independently read the
complete source, proof and dependencies and ran a fresh replay, with no
findings. His separate audit checked192 complete modified-definition
register maps(96 signed),384 modified-parent/manual-finalizer outputs
(192 signed),384 actual24-tile update identities,16 zero-selector cases,
four independent degree/domain/closure ledgers,24 malformed callers,72
literal-query formulas and both independently calculated wrong-power
residues. It also packed63 genuine accepting histories(60 with delimiters),
covering901 actual steps: all retained global/transport comparisons and
the complete joined AND passed. These remain outer/query/source fixtures,
not full native Pell-zero tuples. Seven local links and whitespace passed.
