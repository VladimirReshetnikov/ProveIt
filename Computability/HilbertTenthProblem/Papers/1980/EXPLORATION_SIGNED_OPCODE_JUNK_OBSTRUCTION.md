# Direct signed-opcode reuse fails the unchanged native junk mask

This bounded search examines the complete117 controller of
`EXPLORATION_COMPLEMENT_ZERO_SERIAL_COMPOSITION.md`. Its counter already
computes delta=FKplus-FKminus. Reusing delta in the ROM would remove the
separate subtraction Kplus=FKplus-J. There is a formal **116-operation**
schedule, with56 products and60 additions/subtractions, but its direct
affine junk transformation fails the existing native mask on every
nonempty correctly encoded history. It is not a new represented-history
or universal bound.

The source and finite receipt are
`../verification/explore_signed_opcode_junk_obstruction.py/.json`.
No published predecessor is changed.

## 1. Exact algebra and the apparent saving

Write Kplus=FKplus-J, D=FZbar-J and let V be the predecessor's raw
Boolean junk. The positive sign pair gives

    delta=2Kplus-H.

The cyclic routing equation is

    (RK-g)C=2gIJ+R[V+hs Kplus+hz D].

Twice this equation can instead be written

    (2RK-2g)C=4gIJ+R[Vnew+hs delta+2hz D],
    Vnew=2V+hs H.                              (1)

Every multiplication by2 in the fixed coefficients is free numeral
selection. The already computed delta replaces raw_Kplus, removing one
subtraction. The other route products and additions have the same count.
The exact checker expands all31 source comparisons of this formal116
schedule, including the inherited acyclic auxiliary-norm correction.
All43 supplied positive coordinates are still present.

Equation(1) also shows that Vnew is uniquely determined if the decoded
program path and counter flags are fixed. One cannot choose a different
junk value merely to repair its native mask.

## 2. General obstruction at the first nonzero junk digit

In every canonical predecessor row, V is a nonnegative ternary word
with digits0 or1. Its count-marker unit digit is1. This marker is not a
selected successor or flag output, so V>0 for every nonempty history.
The marker exponent is d, whereas the sign-output exponent is d+bs>d.
Thus the least nonzero digit position e of the complete V satisfies
e<=d<d+bs. The term hs H has no digits at or below e.

There is no incoming carry below e in the prescribed adapter J+Vnew:
J has digit1 everywhere, and Vnew=2V+hs H is zero below e. Its raw
digit at e is therefore

    1+2=3.

The normalized digit is0, which is forbidden by the native digit
alphabet{1,2}. Consequently J+Vnew cannot be a native word. This is a
failure of the proposed canonical converse for every nonempty path,
including arbitrarily large choices of width. Increasing the radix
does not repair a zero at this fixed low position.

The argument does not presume that all possible solutions of the
unproved116 equations decode correctly. It establishes the exact
obstruction to this direct route substitution with the unchanged junk
adapter. It is neither a full spurious positive-solution construction
nor a lower bound on all possible controller encodings.

More generally, even without a sign-offset term, every positive Boolean
ternary word V makes J+2V fail at V's least nonzero digit. No fixed
integer offset can map the two local values0 and2 into the consecutive
native values1 and2 without using a carry or an additional digit.

## 3. Why this does not exclude a different paired-digit representation

A two-position repair exists:

    5+2v = (2,1)_3 when v=0,
             (1,2)_3 when v=1,

where the displayed pairs list the least significant digit first.
Thus spaced Boolean junk could be re-encoded by native pairs. The
complete fixed pattern over an even digit length would be
5(q-1)/8, and the resulting candidate field would be that pattern plus
2V. The old support/TestV equation and all preliminary range bounds
would also need to be rewritten. The pattern is not a free variable
register: q is variable, and division by8 is not a primitive of this
arithmetic model. Directly clearing these factors in both the route
and TestV equations currently costs more than the saved subtraction.
No impossibility or achieved count is asserted for such a redesigned
representation.

## 4. Exact evidence boundary

The maintained checker verifies the formal116 source count, the raw
routing identity, every selected edge in the fixed117 ROM, and all
nonzero Boolean ternary words through eight digits. It checks the
forbidden zero in each proposed native adapter and separately confirms
both paired-digit repairs. These finite checks corroborate the general
least-nonzero-digit proof; they do not replace it or claim a successful
lower-count system.
