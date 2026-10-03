# A filtered paired queue with a five-operation carry controller

The [polynomial-input extension](input_bridge_filtered_polynomial_obstruction.md)
also excludes repair by any fixed positive even integer-polynomial
initial-value substitution alone. Additional filters remain outside that theorem.

A subsequent [raw-input obstruction](native_controller_paired_raw_obstruction.md)
proves that this one-carry family has no universal representation compiler,
including with its paid fixed block alignment. The exact component theorem
and counts below remain valid.

The [paired Boolean ternary FIFO63](native_boolean_pair_fifo63.md) admits
an exact additional local rule

    a0+a1+d0=1.                                           (1)

It costs three operations. When the fixed controller constants satisfy
`2*cf=h+u0`, its full affine carry relation costs only five more operations.
The resulting source has**71=35M+36A**, with20 equations and29 strictly
positive witnesses besides x. This is a finite-machine relation,
not a universal compiler. The required ordinary-input simulation and
acceptance theorem remain open; four operations below76 are unallocated.

Here `d0,d1` are the two read bits, `a0,a1` the two append bits, and a
carry step is

    3*c_next=c+h+u0*d0+u1*d1+v0*a0+v1*a1.                 (2)

All four coefficients, h, and the endpoints cs,cf are fixed integers. The
graph means every integral step satisfying(1)–(2), with no preferred-state
restriction. The ordinary input is represented by two positive Boolean
ternary integers I0,I1 whose sum is2x.

## 1. The paid filter and exact projection

Write F0,F1 for the append words and F2,F3 for the read words. The paired
base supplies q=3^t, W=3^m, positive I0,I1, and

    F2=I0+W*F0, F3=I1+W*F1,
    I0+I1=2x<W, q=W*L.                                  (3)

Each Fi is a positive length-t Boolean ternary word; all four tracks
therefore contain a1. The base also supplies `sum(Fi)<q` and even packed
parity. Its scalar append register A=F0+F1 is already computed.

Compute H as a register using the three additions

    H=A+F2; twiceH=H+H; repunit=twiceH+1,
    repunit=q.                                          (4)

Since q=3^t, H=(q-1)/2 is the length-t ternary repunit. At each position
the residual in `F0+F1+F2=H` lies in[-1,2]. Its units coefficient is
divisible by3 and hence zero; dividing by3 proves every coefficient zero.
Thus(4) is exactly(1), without a carry alias. Conversely(1) gives(4).
It also gives `sum(Fi)=H+F3<=2H=q-1`, so the base's joint bound is automatic.

After one complete queue pass, physical symbols belong to
`{00,10,01}`: an append11 is forbidden. The allowed read/append pairs on
this alphabet are

    00 -> 10 or01; 01 -> 10 or01; 10 -> 00.                (5)

The initial queue may also contain11, which(1) sends to00. This initial
case is not removed from the full accepted graph.

## 2. Cancellation at the forced terminal carry

The exact telescoped version of(2) is

    cs+h*H+u0*F2+u1*F3+v0*F0+v1*F1=q*cf.                (6)

Substitute `F2=H-F0-F1`, `q=2H+1`, and `2cf=h+u0`. Equation(6) becomes

    (v0-u0)*F0+(v1-u0)*F1+u1*F3=cf-cs.                 (7)

Its literal schedule consists of three fixed scalar products and two
additions; compare the result to the fixed numeral cf-cs. There is no
operation for computing a fixed coefficient or the fixed right side.
The filter and controller addition is therefore `3A+3M+2A=8` operations
above63.

Conversely, (7) and(4) recover(6). Reduction modulo3 and successive
division of(6) recover an integral carry at every step, starting at cs
and ending at cf. Thus the equation certifies the whole compatible carry
path, rather than selected edges between suggested state values.

Together with the paired base, the exact projection is a finite t-step
width-m FIFO path from `(I0,I1,cs)` to `(0,0,cf)`, satisfying(1)–(2),
with I0,I1 positive Boolean words summing to2x, and with every one of
the four read/append tracks used. Any such path supplies the base's
positive witnesses. In particular its parity is automatic from

    sum(Fi)=2x+(W+1)*(F0+F1),

since W is odd. No parity restriction on a proposed finite path is omitted.

## 3. Why this endpoint is necessary for unbounded ordinary inputs

This statement concerns the same local filter, initially allowing
arbitrary fixed h,u0,u1,v0,v1,cs,cf. Put

    G=|h|+|u0|+|u1|+|v0|+|v1|,
    C=max(|cs|,ceil(G/2)), B=2C+|h+u0|.

Every carry has absolute value at most C, by induction using(2).
The two zero-terminal transports in(3) force the last m appended symbols
to be00. Equation(1) therefore makes their corresponding primary reads
all1.

The strict positivity of F1 supplies an append01 at some time j: the
filter forces a0=d0=0 there. That physical pair is read at j+m<t, and
its primary read is0. It cannot occur among the final m primary reads,
which are all1. Hence `j+m<t-m`, proving **t>2m** for every admitted run.
Every final m read is consequently an earlier appended symbol; these
symbols never equal11. The final m steps have the single full label
`read10/append00`. No large-width or initial-padding assumption is needed.

On this tail, `b=2c-h-u0` obeys `b_next=b/3`. Hence

    W*|2cf-h-u0|=|2c_(t-m)-h-u0|<=B.                    (8)

If `2cf!=h+u0`, every accepted width satisfies `W<=B`. In particular
`2x<W<=B`, so the accepted ordinary input set is finite, with an explicit
uniform bound depending only on the controller constants. At each of
these finitely many widths there are finitely many initial splits,
queues and carries in[-C,C]. Tracking four additional Boolean flags
records whether each Fi is positive. Exhaustive reachability determines
the exact finite accepted set. This is an effective finite-input
obstruction for the wrong endpoint, not just a heuristic preference
for(7).

When `2cf=h+u0`, (8) instead says that the entire final erasing tail is
already at carry cf. It supplies no width bound and no decidability
conclusion for the filtered family.

## 4. A limitation on direct complete Mealy embeddings

If a finite set of distinct carry states supports arbitrary repetitions
of a fixed physical label, that label acts by `c -> (c+g)/3`.
Its nth iterate differs from its fixed point g/2 by `3^-n*(c-g/2)`.
An infinite integral path in a finite set is possible only at c=g/2:
alternatively `3^n*(2c_n-g)=2c_0-g` forces the integer right side to
vanish once n is sufficiently large.

In particular a complete two-state/three-symbol Mealy machine on(5)
cannot be embedded as two distinct carry values: both states would have
to admit every power of input10, whose output is forced00. This excludes
that direct complete-machine construction. Partial controllers,
context-dependent symbol codes and additional paid filters are outside
the conclusion. No nonuniversality claim for the71 family follows.

## 5. Three paid operations align both block lengths

Fix an integer ell>=2 and the numeral B=3^ell. The filter already computes
twiceH=q-1. Add positive coordinates J,K and

    time_blocks=(B-1)*J; width_blocks=(B-1)*K;
    aligned_width=width_blocks+1,
    time_blocks=twiceH, aligned_width=W.                 (9)

This costs two multiplications and one addition, giving74 operations.
The full ledger is**74=37M+37A**,22 equations and31 positive witnesses
besides x. The71 source computes H as a register, so no H witness or
extra comparison is needed.
It is exactly the restriction `ell|t` and `ell|m`: writing an exponent
as ell*k+r, divisibility by3^ell-1 reduces to divisibility of3^r-1;
for0<=r<ell that is possible only when r=0. Conversely both geometric
quotients are positive integers. Thus the same fixed-length macro blocks
align in the temporal word and in the queue delay. No block alphabet,
phase mask or ordinary-input recoding is supplied by(9).

## 6. The66 filter alone admits every ordinary positive input

The base plus(4), without a carry equation, costs**66=32M+34A**, with19
equations and29 positive witnesses besides x. This relation is
nonempty for every positive x. Choose a power W=3^m>6x and any positive
Boolean split I0+I1=2x. Such a split exists: a trit2 can be shared; if
there are no2s, the positive even integer2x has at least two1s to split.
Put Hm=(W-1)/2 and q=W^3. In the first sweep append `(0,1-d0)`; in the
second append `(1,0)`; in the third append `(0,0)`. These choices satisfy
the filter because the primary queue is zero in sweep two and all1s in
sweep three. They give

    F0=W*Hm, F1=Hm-I0,
    F2=I0+W^2*Hm, F3=I1+W*(Hm-I0).                     (10)

All fields are positive; W>6x gives a zero top trit of I0, so F1>0.
They are Boolean ternary words with disjoint sweep positions. Formula(10)
has zero terminal queues and `F0+F1+F2=(q-1)/2`. The joint bound and
parity follow from Section1, and the positive base converse applies.
This construction supplies no carry path for arbitrary controller
constants; it only proves the unfiltered66 relation accepts every x.

## 7. Positive controlled witness and evidence

Take x=1, W=3, q=81 and

    (F0,F1,F2,F3)=(9,3,28,10), I0=I1=1, H=40.

The four physical steps are

    11 -> 00, 00 -> 01, 01 -> 10, 10 -> 00.

All four words are positive, their sum is50<81, and both transports
hold. With append weights(-2,4), read weights(2,3), h=-2 and cs=cf=0,
the carry sequence is(0,1,1,0,0). Equation(7) is
`-4F0+2F1+3F3=0`. The remaining outer positive values are alpha=31,
width_beta=1 and L=27. The base's proved converse supplies its Pell
coordinates; the huge complete tuple is not materialized here.

The [checker](native_controller_paired_filter71.py) independently expands
all source polynomials and the inherited auxiliary-norm correction in the
complete66/71/74 DAGs. The [receipt](native_controller_paired_filter71.json)
records53,108 positive Boolean field tuples,37,320 local-word/controller
cases,200 explicit ordinary-input maps,6,300 block-alignment cases, and
573 reachable finite configurations testing the terminal bound. The
finite checks supplement the parametric projection and positivity proofs.
Independent full proof, source and fresh default-replay review passed.
