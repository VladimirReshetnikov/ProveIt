# Two paid selector sums give a399-operation Tseytin polynomial

> The later [digit-permutation construction](tseytin_permuted_digits387.md)
> reaches387 operations with62 witnesses and degree at most4712.
> It recompiles program numerals and histories. This note retains the
> distinct source and precise equivalence claim of its own stage.

The [literal source](tseytin_adjacent_coefficients399.py) removes two
multiplications from the [computed-field401 compiler](tseytin_computed_fields401.md).
The complete universal polynomial costs **399=186M+213A**, with385
certificate operations, five comparisons,62 positive witnesses, one fixed
positive program parameter, ordinary positive input, and degree **at
most4712**. The separate-power form costs401 and has degree at most4752.
The corresponding SOS bounds are9396 and9288, at the same respective
operation totals. The [receipt](tseytin_adjacent_coefficients399.json)
contains all four complete schedules.

This change is an exact polynomial identity on identical supplied integer
coordinates. It preserves the full positive zero set, all program/input
interfaces and every domain of the401 parent. Its complete universality
and native sign arguments therefore transfer directly. It does not alter
the independent75 certificate /87 polynomial operation bounds.

## 1. Reuse the physical selector-class sums

The actual C2 affine updates contain the two fragments

    316 Shat14+317 Shat16,
    316 Shat15+317 Shat17.

Their input sums are already paid by the physical selector-class graph:

    group_sum__221=Shat14+Shat16,
    group_sum__228=Shat15+Shat17.

For arbitrary integers a,b,

    316a+317b=317(a+b)−a.                            (1)

For each fragment, replace its pair of coefficient multiplications and
its two additions into the preceding accumulator by one multiplication
of the existing sum, one subtraction of a, and one accumulator addition.
Thus **one multiplication disappears per fragment**. The subtraction
replaces a multiplication, and one former accumulator addition disappears;
the total number of additions/subtractions stays unchanged. Multiplication
by the fixed numeral317 is still charged.

Concretely the upper fragment becomes

    linear_coefficient__398=317*group_sum__221,
    linear_coefficient__397=linear_coefficient__398−Shat14,
    linear_sum__405=linear_sum__404+linear_coefficient__397.

Delete `linear_sum__406` and alias its sole consumer to `linear_sum__405`.
The lower fragment analogously uses `linear_coefficient__417`,
`linear_coefficient__416`, `group_sum__228`, and `linear_sum__424`, deleting
`linear_sum__425`. All subsequent affine update and transport registers
are exactly unchanged. A topological sort puts the already paid selector
sums before their new consumers.

The guard accepts only the complete canonical401 parent. It checks all
ten defining rows and each changed coefficient/accumulator's exact private
consumer. The output and degree APIs likewise require the entire canonical
successor, including interfaces, supplied coordinates and recipe. This
prevents applying the local identity to a caller that separately exposes
one of the old coefficient registers.

## 2. Full source, domain and degree identity

Six retained intermediate values change: the four named coefficient
registers and the two shortened accumulators. Their explicit meanings
are given by(1) and the displayed rows. Each shortened accumulator equals
the corresponding *deleted* old accumulator. Every other retained register
is unchanged on every integer assignment. In particular every final unit
factor, ordinary comparison and complete polynomial is identical to401.
No positive coordinate is eliminated or remapped, and no private native
extension needs to be reconstructed for this step.

All altered fragments are degree1 in the supplied selectors. The complete
retained degree dictionary is therefore unchanged, including the two
main-norm cancellations and the factored native index. The parent's
conservative degree bounds4712/4752, or9396/9288 for SOS, apply verbatim.
These are upper bounds rather than exact total-degree claims.

Default execution independently regenerates the saved receipt; `--write`
rewrites it. The audit compares every unchanged retained register, both
explicit coefficient identities, both shortened accumulators, all four
complete polynomial forms, both degree dictionaries and output closure.
It includes384 complete output identities(192 signed assignments),12
zero-selector contexts, and24 malformed parent/successor rejections.
These are exact source/component tests; the all-integer proof is(1).
Author generation and fresh replay pass. Independent full proof/source
review and a separate fresh replay passed with no findings. Its independent
executor checked192 full manual register maps(96 signed),384 complete
parent/manual-finalizer outputs(192 signed),16 zero-selector contexts,
all four cancelled-norm degree/opcode/domain/closure ledgers and16 extra
nested-export guard rejections. All three local links and whitespace pass.
