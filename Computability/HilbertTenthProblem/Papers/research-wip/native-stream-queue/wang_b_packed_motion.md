# A paid uniform tape-and-head history for four Wang primitives

One prescribed native AND certifies a nonempty chronological sequence
of mark/stay, read/stay, left and right operations, with explicit initial
and final tapes and heads. The [source](wang_b_packed_motion.py) costs
**188=81M+107A**, with **19 comparisons and35 positive witnesses**.
Its single SOS polynomial costs **244=100M+144A** and has total degree
**at most316**. These counts are independent of the duration. The
[receipt](wang_b_packed_motion.json) records the complete literal DAG.

This extends the chronological [packed tape packet](wang_b_packed_tape.md)
by paying for nearest-neighbor head motion. The four positive parameters
are initial_tape_hat, final_tape_hat, initial_head and final_head. The
tape hats encode nonnegative tape integers by adding1; the unshifted
heads are proved to be powers of two. The head cannot move left from
the lowest represented cell. Every finite physical run can be translated
into such a finite nonnegative window, but that translation does not
provide a TM-input morphism or finite instruction control.

The action choices here are existential and unconstrained by a program.
No universal computation or improved universal operation count follows.
In fact Section6 identifies the simple endpoint relation obtained when
all internal history choices are forgotten.

## 1. Paid coordinates and bounds before typing

Write T0=initial_tape_hat−1 and Tf=final_tape_hat−1, and let H0,Hf
denote the two positive head parameters. Supply positive hats for the
ten potentially zero words

    T,G,C,I,W,V,L,R,MH,LH,

as well as positive Stay_hat, height_slack and global_bound. Together
these are13 outer witnesses. The22 positive native AND auxiliaries
bring the total to35. Each displayed word is its hat minus1. Put

    D=initial_tape_hat+final_tape_hat+H0+Hf+height_slack,
    Bhalf=4D, B=Bhalf+Bhalf=8D,
    Stay=Stay_hat−1,
    J=I+L+R+Stay,
    Move=L+R,
    Pminus=(B−1)J, P=Pminus+1,
    H=G+J.                                           (1)

The source computes J directly from the four action hats, using their
sum minus4. Consequently

    0<=I<=J, 0<=L<=Move<=J                           (2)

hold on every positive supplied assignment, before any equation.
This is important: computing a mask from a free selector word and only
later trying to type that selector could introduce a carry between the
joined lanes.

The first outer comparison is

    J+sum_(ten words X) X_hat+global_bound=P.          (3)

At a zero, J=0 would give P=1 while the left side is at least11.
Thus J>0 and P>=B>=40. Every one of the ten words, and H=G+J,
lies strictly below P. The selected-row masks

    MI=(B−1)I, MM=(B−1)Move, ML=(B−1)L

lie between0 and P−1 by(2). The range mask MD=(D−1)J is also
strictly below P. All these are canonical lane coefficients without
assuming powers of two or any decoded row semantics.

For example, if one instead let a free Move equal B−1 while J=1
and P=B, then

    (B−1)Move=1+(B−2)P,

which carries into the next joined lane. The four-action decomposition
in(1) rules out this untyped configuration; no hidden selector bound
is supplied by the later AND.

## 2. Twelve canonical lanes and one native scale

Join the following coefficients in increasing powers of P:

| Lane | First input | Second input | Output |
|---:|---|---|---|
|0|H|G|0|
|1|T|H|C|
|2|H|MI|W|
|3|C|MI|V|
|4|I|J|I|
|5|T|MD|T|
|6|G|MD|G|
|7|Move|J|Move|
|8|L|Move|L|
|9|H|MM|MH|
|10|H|ML|LH|
|11|I|Move|0|

Denote the three joined integers by A,M,Z. Each lies in[0,P^12)
by Section1. Use the prescribed native scale

    S=B*P^12.                                       (4)

Both positive factors B and P become dyadic when the complete native
AND theorem types S as a power of two. Thus no separate joined lane
for B AND(B−1)=0 is needed. This product-scale method was also identified
independently while constructing the
[packed toggle packet](langton_ant_packed_toggle_tape.md).
The source pays five multiplications for P²,P⁴,P⁸,P^12 and B*P^12.

All three joined words are nonnegative even off the zero set on the
declared positive domain. The native inputs A+1,M+1,Z+1 are therefore
legitimate positive hats. The source folds them into exactly the paid
ports16A+12,16M+10,16Z+8 and native scale16S. It retains all64 gates,
16 comparisons and22 auxiliaries of the complete
[prescribed-scale AND](native_binary_masked_selection63.md).

The native theorem gives S dyadic and Z=A AND M. Hence B and P are
dyadic. The exact repunit relation P−1=(B−1)J and J>0 then give

    P=B^t, J=1+B+...+B^(t−1), t>=1.                 (5)

Also D=B/8 is dyadic. Because all twelve P-lane coefficients were
already canonical, there is no overlap or carry in splitting the
joined AND into the twelve displayed scalar identities.

In base B, the range identities give0<=T_i,G_i<D. Therefore
H=G+J has digits H_i=G_i+1 in[1,D], with no carry. The first lane
gives H_i AND(H_i−1)=0, so every head is a positive power of two.
The second gives C_i=T_i AND H_i, hence C_i is0 or H_i.

Lanes4,7,8 give Boolean I_i, Move_i and L_i, with L_i<=Move_i.
Because R=Move−L, its digits are also Boolean and disjoint from L.
Lane11 excludes I_i=Move_i=1. Consequently
I_i+L_i+R_i is0 or1, and the exact identity
Stay=J−I−L−R makes Stay the canonical Boolean complement. Exactly
one of mark, left, right or read/stay is chosen in each row.

The remaining selection lanes then give

    W_i=I_i H_i, V_i=I_i C_i,
    MH_i=Move_i H_i, LH_i=L_i H_i.                   (6)

Their masks are canonical base-B row masks: each selected row contains
B−1 and each unselected row contains0. The selector typing and the
earlier unconditional P-lane bounds have distinct roles; neither is
assumed in place of the other.

## 3. The two chronological comparisons

Keep the tape comparison from the previous packet:

    B*(T+W−V)+T0=T+P*Tf.                            (7)

Its literal version uses the two supplied tape hats and the already
paid Pminus. By(6), the next-tape digit is

    T_i+I_i(H_i−C_i),

which is nonnegative and at most2D−1<B. The two endpoint tapes are
less than D by the definition of D. Unique base-B expansion of(7)
therefore gives the initial tape, each successive tape and the final
tape exactly. Marking sets the selected bit, including an idempotent
mark on an already marked cell. The other three actions leave it alone.

The new paid head comparison is

    B*(H+MH−LH)+H0=H+P*Hf+Bhalf*LH.                 (8)

There is no uncharged division by2: Bhalf=4D is computed explicitly
and B is its paid double. Multiplying(8) by2 only in the proof gives

    B*[2(H+MH−LH)−LH]+2H0=2H+2P*Hf.                (9)

The bracketed word has row coefficients

    H_i for left, 2H_i for either stay, 4H_i for right.

All are positive and at most4D<B. The current doubled-head digits
are at most2D<B, and both doubled endpoint heads are strictly less
than2D. Thus every word in(9) is canonical. Digit uniqueness gives
H0=H_0 and the exact rules

    H_(i+1)=H_i/2  on left,
    H_(i+1)=H_i    on mark or read/stay,
    H_(i+1)=2H_i   on right,                          (10)

with H_t=Hf. A left move from H_i=1 would require the integer next
head to satisfy2H_(i+1)=1, which is impossible. The initial head is
dyadic because it equals the typed first-row head; the final head is
dyadic by(10). Their typing is part of this certificate.

The read information C_i remains chronological: it belongs to the
current tape and current head, before either the mark or motion.
There is no choice of a final tape used to justify earlier reads.

## 4. Complete positive converse

Take any finite nonempty sequence of the four stated primitives on
a nonnegative binary tape, with heads2^p for p>=0 and no left step
at p=0. Let its duration be t, and suppose its endpoint parameters
are the four supplied values. Choose a dyadic D>=16 strictly larger
than every tape integer and head in the trace, and also larger than
the sum of the four positive parameters. Set B=8D,P=B^t and J
as in(5).

Pack every row quantity in the table and add1 to form each positive
hat, including the packed read/stay action in Stay_hat. The action partition gives
J=I+L+R+Stay exactly. The positive height slack is D minus the sum
of the endpoint parameters. All selections and both transports hold.

For the global slack, the first six raw words obey the same coarse
bound as before,

    T+G+C+I+W+V <= (5D−3)J.

The other four obey L+R<=J and MH+LH<=2DJ. Hence the sum of all
ten raw words is at most(7D−2)J, and

    global_bound=P−J−sum_X X_hat >= D*J−9>0.          (11)

This is a genuine positive coordinate even at duration1; completeness
is free to choose the larger dyadic D. No fixed supplied upper duration
is assumed. Both native inputs are below P^12<S, their exact AND is
the packed output, and S is dyadic. The full prescribed-scale native
converse supplies all22 remaining positive witnesses. The finite checks
below do not replace that complete native extension.

Every finite physical Wang path over integer cell positions has a
finite visited region. A sufficiently large common spatial translation
makes all relevant cells nonnegative and gives the interface above.
The numerical endpoint tapes and head powers must be translated
consistently. This observation does not turn ordinary TM input into
these endpoint parameters for free.

## 5. Literal cost, degree and concrete rejected shortcuts

The wrapper has124=48M+76A gates. Adding the unchanged64=33M+31A
native core gives188=81M+107A. There are three outer comparisons
and sixteen native comparisons. Nineteen residuals, squares and
their sum add19M+37A, giving244=100M+144A. All fixed-numeral
multiplications and both endpoint transports are counted.

The folded head comparison costs3M+5A. Paying the half radix and
forming B by addition saves two total gates compared with computing
both doubled endpoint heads and the doubled next-head word literally.
The proof-only multiplication of equation(8) by2 is not a source gate.

Each parameter and positive witness has degree one. D,B,J have degree
at most1, P at most2, and S=B*P^12 at most25. The largest propagated
native residual bound is158, giving the SOS bound316. No use of the
zero-set equations lowers those polynomial bounds; no exact degree
is claimed.

The receipt retains three boundary checks with positive outer data.
A one-row left move at head1 passes every other outer comparison and
all joined bit lanes, but its head residual is−B/2. A forged stay from
head2 to head8 likewise fails only head chronology. Finally, omitting
the last exclusivity lane would permit a simultaneous mark-and-left
first row: at D=16,B=128,t=2, take I=L=Move=1,R=0 and Stay=B−1.
The three outer equations and all eleven lower bit lanes hold, but the
top lane has I AND Move=1 instead of0. This is a row-semantics failure,
not a purported false endpoint or universal-input counterexample.

## 6. What remains outside the batch theorem

With all action choices existential, the endpoint projection is exactly

    H0,Hf positive powers of two, and T0 AND Tf=T0.    (12)

Necessity follows from typed heads and non-erasing marks. Conversely,
when(12) holds, visit each finitely many missing marked cells of Tf,
mark them, and walk to the final head. All cell indices can stay
nonnegative. Add a read/stay step if needed to make the trace nonempty.
Section4 then gives a positive certificate. Thus this unrestricted
endpoint language is decidable and carries no universality claim.

A complete Wang program compiler must still require the correct
instruction at every row, connect read bits to conditional control,
enforce the initial and accepting control states, and pay for its
ordinary-input representation. Those tasks are not charged by this
packet. Its contribution is the full uniform tape/head/action batch,
with pretyping bounds and both chronological transports already paid.

## 7. Exact source checks and review scope

The writer checks384 complete residual/SOS identities,192 signed,
against a separately assembled canonical AND64 invocation. All192
positive assignments also check the unconditional selector inequalities
and canonical mask bounds. It constructs288 genuine outer paths of
lengths1 through12, with all four action kinds, and checks every outer
comparison, joined AND and prescribed-scale bound. Another576
independent canonical-digit tests check the head-transport equivalence;
the local primitive table includes explicit lowest-cell rejection.

These paths use placeholder native coordinates and are not claimed to
be numerical full Pell zeros. The positive native witnesses are supplied
by the complete converse in Section4. Arbitrary signed residual identities
make no positivity or physical-path claim.

```sh
python3 wang_b_packed_motion.py
```

Author receipt generation and fresh default replay pass. Root full
proof/source review and fresh default replay pass without findings,
including the pretyping action bounds, both integer transports,
positive converse and endpoint-projection scope.

A second independent full proof/source review and refreshed default
replay also pass without findings. Its separate executor checked192
complete native-residual/SOS identities,96 signed. A separate physical
set-of-cells simulation supplied128 freshly packed prefixes with1,616
steps,355 left moves and18 starts at cell0, without using the author's
path or independent-assembly helpers. These are outer-history checks,
not expanded full native Pell solutions. The final rejected-shape
checks were also replayed.
