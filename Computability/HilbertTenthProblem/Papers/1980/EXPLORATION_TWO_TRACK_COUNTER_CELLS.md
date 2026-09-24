# Six-operation counter cells with a two-operation raw input link

This is a concrete local component for a possible binary-counter history
compiler. It is not a complete universal certificate or a reduction of the
published universal bound. The complete register selection, zero test,
control transition and terminal interface have not been encoded.

The source model is the strongly universal increment/conditional-decrement
register machine audited in `EXPLORATION_RAW_INPUT_TRACKS.md`. Its input
contract accepts a fixed program index and the original numerical query.
That contract makes it a more direct candidate here than a simulation
which first replaces the query by a unary displacement or a prime power.
The present note concerns the local arithmetic only; it does not claim
that the source machine's instruction count is its certificate size.

## 1. The raw query needs two Boolean tracks in radix four

For radix-four Boolean words I0,I1, the equation

    x=I0+2I1

has a unique nonnegative solution for every nonnegative x. The tracks
contain its even and odd binary bits at the corresponding radix-four
positions. The link costs one multiplication and one addition. The proof
and its primary-source context are in `EXPLORATION_RAW_INPUT_TRACKS.md`.
Booleanity, common alignment and positive representations of zero tracks
are separate obligations; this equation supplies none of them for free.

## 2. An increment cell

A physical cell holds two counter bits a0,a1. Its numerical digit is
a0+2a1. Let c be the carry entering this two-bit cell; d is the internal
carry, and e is the outgoing carry. All seven variables below are Boolean.
The two equations

    a0+c=b0+2d,
    a1+d=b1+2e                                      (1)

have a unique solution b0,b1,d,e for each a0,a1,c. The first equation is
the ordinary half-adder. Its two sides range from zero to three, and the
second equation has the same property. Consequently (1) is equivalent to

    b0+2b1=(a0+2a1+c) mod 4,
    e=floor((a0+2a1+c)/4),
    d=floor((a0+c)/2).

When each letter is an aligned radix-four Boolean word, the same two
integer equations hold at every position independently. Every raw digit
on each nonnegative side is at most three, so equality has no inter-cell
carries. This is a coefficient argument, not an assumption about the
normalized digits of a signed residual.

The explicit schedule is

    a0+c, 2d, b0+2d, a1+d, 2e, b1+2e.

It contains six operations, two multiplications and four additions,
followed by two free equality tests. The numeral two is free, and each
multiplication by it is counted.

## 3. A conditional-decrement arithmetic cell

For an entering borrow c, reverse the positions of the doubled terms:

    a0+2d=b0+c,
    a1+2e=b1+d.                                    (2)

The same six-operation count and carry-free packing proof apply. The
unique result is

    b0+2b1=(a0+2a1-c) mod 4,
    e=1 if a0+2a1<c, and e=0 otherwise,
    d=1 if a0<c, and d=0 otherwise.

This is an arithmetic borrow cell, not yet a machine's conditional
decrement instruction. A register machine branches on whether the entire
register is zero. The final outgoing borrow can report underflow if the
least-significant entering borrow is one, all inter-cell borrows are
correctly linked, and the register ends are enforced. Those conditions
must still be represented by the complete history equations.

## 4. The missing compiler is explicit

These equations show that raw binary counter bits are compatible with a
small exact radix-four local relation. They do not close the following
shared-history requirements:

* Adjacent cells must link outgoing and incoming carries or borrows, with
  one seed at the selected register's low end and the correct behavior at
  every other register boundary.
* A control word must select increment, decrement or no change. Equations
  (1) and (2) are different relations. Using a scalar product of two packed
  words as a positionwise selector is invalid: it performs convolution.
* The high-end borrow must select the correct zero/nonzero successor state,
  and the control state must advance according to the fixed program.
* Initial registers, the variable raw query, accepting control state,
  finite exterior, all field ranges and every possibly zero auxiliary need
  complete integer equations and an operation count.

There is also a useful cancellation warning. Combining the two increment
equations gives

    A0+2A1+C=B0+2B1+4E.

If one were to assert C=S+4E for a seed word S, this reduces to a global
addition of S. It does not by itself prevent a carry from overflowing into
an adjacent register block. Bounds or boundary tests remain necessary.
This explains why the six local operations cannot be promoted to a
whole-machine verifier by an uncounted shift convention.

## 5. Exact finite checks

`../verification/explore_two_track_counter_cells.py` checks all Boolean
assignments of a cell for both modes, uniqueness for every input, and all
two-cell assignments against the packed equations. It also constructs
finite ripple chains for every counter value through eight bits and checks
the input link, increment result, decrement result and final carry or
borrow. These are finite checks of the local lemmas. No universal machine,
positive Pell extension or complete history certificate is instantiated.
