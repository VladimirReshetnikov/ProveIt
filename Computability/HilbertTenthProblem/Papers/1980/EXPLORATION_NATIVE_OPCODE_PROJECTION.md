# Two paid operations per native opcode projection in a fixed frame

This is an exact adapter to the fixed nondeterministic router in
`EXPLORATION_NONDETERMINISTIC_PROGRAM_ROUTING.md`. It saves the separate
native-to-raw subtraction in that note's conditional projection interface.
It is **not** a complete counter/router system or a universal bound. The
flag must already be typed by a counter component with the same q and
frame. The fixed-frame qualification is essential.

The independent symbolic schedule and finite projection checks are in
`../verification/explore_native_opcode_projection.py/.json`.

## 1. Exact identity and count

Write J=(q-1)/2. Suppose the counter supplies a positive native flag
Fk=J+Q, where the decoded raw Q is a Boolean subset of the row-head mask
H. With the additional flag output coefficient h fixed, the intended
routing equation is

    (WK-g)C+gI=(gF)q+W(V+hQ).                     (1)

All W,K,g,I,F,h are fixed integers for the compiled router. Substitute
Q=Fk-J, double (1), and use 2J=q-1. The result is

    [2(WK-g)]C+(2gI-Wh)
        =(2gF-Wh)q+2W(V+hFk).                     (2)

The full seven-operation schedule for (2) is

    a = [2(WK-g)]*C
    left = a+(2gI-Wh)
    b = h*Fk
    c = V+b
    d = (2gF-Wh)*q
    e = (2W)*c
    right = d+e.

It uses four multiplications and three additions. The unprojected routing
calculation costs three multiplications and two additions, so the
increment is exactly **one multiplication and one addition**. No J or Q
register is computed by this adapter. The fixed integer coefficients may
be negative; the certificate permits signed computed intermediates and
free fixed integer numerals. No existential variable is reinterpreted as
a signed variable.

For an explicit source comparison, let R be left minus right in (1),
with Q replaced by Fk-J, and let Rnew be the residual of (2). Then

    Rnew-2R = Wh(q-2J-1).                         (3)

Thus replacing the routing equality is reversible once the counter's
existing q=2J+1 equation holds. Every supplied witness, including V,
TestC, TestV and the counter's Fk, remains the same positive integer.

For k native flags with fixed coefficients h_i, let hsum=sum_i h_i and
replace hFk by sum_i h_i Fk_i. Replace Wh in the two fixed coefficients
by W*hsum. The schedule uses k products for the flags, k additions to
accumulate them into V, and the same five other routing operations. Its
cost is 5+2k. Equation (3) becomes W*hsum*(q-2J-1).

## 2. Decoding and the proof-order boundary

Use the router's extended spaced Sidon support: state coordinates are
l*3^i, and the fresh flag coordinates are later distinct values of this
sequence. Add the corresponding flag terms to K and forbid their output
positions in V. Enlarge the fixed frame and adjust the spacing parity as
in the router proof. In particular all distinct target channels remain
separate from the full count-marker block.

The modified equality does not change either support equation or the
shared positive bound. Therefore the router still has its original
pre-mask ranges C<TestC<q and V<TestV<q. No lower bound Fk>=J is used to
derive these ranges. A joint construction must separately establish its
counter-side ranges and the hypotheses of the single shared mask.

After that mask has typed the native counter flag, Q=Fk-J is a Boolean
subset of H. Equation (3) restores (1) exactly. At the flag output
position, KC has the emitted program-label bit, hQ has Q's bit, and V is
zero. The target therefore equates the flag with that label. This is the
same conditional projection proof as for a supplied raw flag. Other
outputs and the count marker are unchanged. In the converse, choose the
already native Fk=J+Q; the same positive V and Test fields satisfy (2).

The argument does not claim that the polynomial equation (2) alone types
Fk, or that its native baseline can be assumed before masking. It also
does not test whether a designated counter is zero. Those obligations
remain part of a complete machine compiler.

## 3. Variable frames are a separate cost problem

When W is variable, neither 2(WK-g), Wh, 2gI-Wh, 2gF-Wh nor 2W is a
free fixed numeral. The seven-operation schedule therefore does not apply
unchanged to the variable-frame raw counter components. The identity
remains valid, but all variable products and sums must be charged and any
reuse justified in the complete shared schedule. In particular this note
does not reduce the published count of any variable-frame component.

## 4. Exact finite evidence

The checker verifies the residual identity for one and three flags,
checks the seven-operation schedule instruction by instruction, and
constructs the enlarged constant table for finite labelled graphs. It
checks canonical projected paths, all Boolean head-subset flags on those
paths, the original and transformed routing residuals, field masks,
positive support slacks, and fixed-sign parity. A false typed label is
required to fail the transformed equality. These finite cases supplement
the general algebraic identity and the previously proved router support
argument. No complete joint counter/router mask or enormous Pell witness
is claimed or numerically instantiated.
