# A paid ternary marker and a complete positive erasing construction

The [hidden Boolean-carry queue64](native_controller_boolean_carry70.md)
has an exact ordinary-input language before adding an external controller:
it accepts x if and only if the ternary expansion of2x contains a digit2.
Here is a constructive proof of the previously missing converse. At
width m, a valid positive erasing run can be chosen in at most5m-2 steps.
A separate odd cycle makes the duration even whenever the width is even
and at least4, without changing the input or terminal condition.

Consequently replacing2x by the fixed affine input **6x+2** costs one
addition and gives a bare filtered component in **65=32M+33A** admitting
every positive ordinary x. The exact external-controller variants cost
71, or73 with even width and duration; symmetric read coefficients give68.
The input marker and all bounds are paid. These are complete arithmetic
components, not universal representations. The erasing construction does
not claim to follow an arbitrary chosen external controller or compute a
program before erasing its data. Universal simulation and acceptance remain
unproved, and the complete universal bound remains76.

## 1. Scalar queue semantics preserve both physical rails

The physical hidden-carry step is

    3e_next=e+2a0+a1+d0+d1-2, e in{0,1}.               (1)

The two queue rails are Boolean. Their sum is a scalar ternary queue,
whose head trit is r=d0+d1 and appended trit is a=a0+a1. There is no
carry when adding the two rail words. The scalar transition table is

| e | r | a | e_next | Physical append |
|---:|---:|---:|---:|---|
|0|0|1|0|10|
|0|1|1|0|01|
|0|2|0|0|00|
|0|2|2|1|11|
|1|0|1|0|01|
|1|1|0|0|00|
|1|1|2|1|11|
|1|2|1|1|10|

The physical orientation of a read sum1 does not affect (1). Every
scalar path therefore lifts from **any supplied initial Boolean split**
to genuine physical queue paths, using the unique append pair listed.
The two rail queues determine the actual read bits at every step. A
zero scalar endpoint is equivalent to both rail endpoints being zero.

At e=0, the alphabet{0,1} is closed and every step appends1. Thus a
positive-duration zero endpoint is impossible for an initial word without
a2. This proves necessity, at every width and for every initial split.

## 2. Normalizing any word containing2

All queue words in this proof are written low-first. Let a width-m word
contain a2 and start with hidden state0. Assume first that m>=2. Let j
be the index of its last2, with0<=j<m.

Process its first j trits in state0, choosing append0 at a read2 and
append1 at either read0 or read1. All processed append trits belong to
{0,1}; the still-unread suffix after the last2 also belongs to{0,1}.
When that last2 reaches the front, choose append2 and enter state1.
The queue now consists of m-1 trits in{0,1}, followed by a marker2.

Let b be its next trit. Exit state1 immediately: append1 if b=0, or
choose append0 if b=1. Both choices return to state0. Process the next
m-2 trits, each in{0,1}, appending1. The resulting configuration is

    queue 2,(1-b),1^(m-2), hidden state0.               (2)

This has taken j+m steps. If b=0 it is already the normalized word

    M_m=2,1^(m-1), hidden state0.                      (3)

If b=1, perform one further sweep: enter state1 at the marker2, read
the following0 and append1 to return to state0, then append1 at each
of the remaining m-2 reads1. This reaches (3) after another m steps.
Normalization therefore takes at most3m-1 steps. At least one transition
has appended11, so both physical append tracks have been used.

## 3. Erasing the normalized word

From (3), enter state1 at the marker, keeping append trit2. At the next
m-2 reads1, choose append2 and stay in state1. At the final read1,
choose append0 and return to state0. The queue is now2^(m-1),0.
Erase the remaining m-1 twos by choosing append0 in state0. Both queues
are empty, with hidden state0. This takes exactly2m-1 further steps.

Together with Section2, the duration is at most5m-2 and is strictly
greater than m. The original input contains a trit2, so both physical
read tracks are positive as well. Thus all four full stream words are
strictly positive; this is not just scalar reachability with empty tracks.

For m=1, the only scalar word containing2 is the one-trit word2. Use
the three transitions

    (2,0)->(2,1)->(1,1)->(0,0).

Their physical appends are11,10,00. Both read tracks and both append
tracks are nonempty, the duration3 equals5m-2, and it exceeds m.

For any positive even initial value I containing2, split its trits into
two Boolean words I0,I1. Each2 is split as1+1, so both words are positive.
The construction works for any width with3^m>I, without a special padding
pattern. Its words satisfy the exact hidden-carry equality

    2F0+F1+F2+F3=q-1,

both paired transports, and the strictly positive joint slack F0+1.
The total field parity is

    sum Fi=I+(W+1)(F0+F1),

which is even. Hence the reviewed positive Boolean/Pell converse supplies
every remaining arithmetic witness at these actual fields. This proves
the full bare64 language statement in the introduction for I=2x.

## 4. An explicit odd loop repairs time parity

One cannot append a zero-time padding step after the empty endpoint:
at e=0 a read00 forces a nonzero append. Instead use the following cycle
at the intermediate marker word (3), for every m>=3.

1. At the marker2 append2, entering state1. At the next1 append2 and
   stay in state1. At the next1 append0 and return to state0.
2. Copy the remaining m-3 leading1s in state0. The queue is
   `2,2,0,1^(m-3)` after m steps.
3. Erase its first2 in state0. At its second2 append2 and enter state1.
   At the following0 append1 and return to state0.
4. Copy the next m-3 leading1s. The queue is `0,2,1^(m-2)` after2m
   steps. At its first0 append1 in state0, returning exactly to (3).

Every transition is in the table. The total length is **2m+1**, odd.
Choose an even m>=4 with3^m>I. After normalization, insert this loop
once if the subsequent cleanup would otherwise give odd total duration.
Then perform Section3. Both m and t are even, and

    m<t<=7m-1.

The positive square roots of W=3^m and q=3^t therefore exist, so the
two paid square comparisons of the aligned source are satisfied. The
loop is a mathematical choice of witness history, not an additional
arithmetic operation or an assertion that every controller permits it.

## 5. One paid addition supplies a marker for every ordinary input

For varying ordinary x>0 set I=6x+2=3(2x)+2. Its units trit is2,
independently of x. In the existing source replace the instruction2x
by6x, then add2. The fixed numeral multiplication remains one paid
multiplication, and only the addition is new. Replace the two uses of
the initial register in the split equation and width bound, and the
scalar transport's use as well. All equations use this same computed I.
The fixed program numerals do not depend on x.

The complete schedules audited by the checker are:

| Variant | M | A | Total | Equations | Positive witnesses besides x |
|---|---:|---:|---:|---:|---:|
| Marker input and hidden filter |32|33|65|19|29|
| Symmetric-read external controller |34|34|68|20|29|
| General external controller at the compatible endpoint |35|36|71|20|29|
| Same with even time and width |37|36|73|22|31|

The general controller still satisfies the proved fixed endpoint condition
`2cf=h+u0+u1`. The exact reduced equation, whole-graph interpretation,
hidden carry semantics and positivity requirements are unchanged. For
every proposed controlled path from a positive split of6x+2, the same
full positive arithmetic converse applies. This is not a proof that every
x has a path under arbitrary nonzero controller constants.

The bare65 component admits every positive x by Sections2–3. With zero
external controller data, the aligned73 source also admits every x by
Section4. These witness constructions are proved parametrically; they
are not inferred from the finite reachability checks.

## 6. Evidence and scope

The checker expands every equation in all four literal modified sources,
including the inherited norm correction. It separately verifies the
physical lifting of the scalar construction, positivity of all four
fields, exact transports, hidden carry endpoints, and time bounds. It
also checks the explicit odd cycle and compares the proved bare scalar
criterion with complete finite reachability graphs.

Every large Pell coordinate is provided by the existing positive converse,
not numerically materialized here. No extra external-controller path,
universal macro-code typing, simulation or halting interpretation is
claimed. Independent full proof, source and fresh default review passed,
including all positive-domain, one-cell and parity-alignment boundaries.
