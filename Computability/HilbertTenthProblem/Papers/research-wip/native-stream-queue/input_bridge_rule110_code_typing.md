# Existing FIFO geometry does not type the serialized01/10 candidate

The fixed two-trit Rule110 candidate has carry codes A=0,B=8,C=4,
read weights(-88,-40), append weights(8,4), offset27, and low-first
symbol codes0=(0,1),1=(1,0). Its correctly typed block relation is useful,
but neither FIFO transport nor eventual zero acceptance supplies that
typing. This note gives an actual accepted FIFO run starting from a
correctly coded initial queue and consuming its own uncoded outputs.
It also excludes free rail identification for this particular candidate.

The result does not address a redesigned code, a phased code filter,
or a universal compiler for the general carry family. In particular it
does not apply to the separate00/12 candidate. The complete universal
bound remains76.

## 1. A complete accepted uncoded run

Take W=81=3^4 and initial queue I=30, whose four low-first trits are
(0,1,0,1), two correctly coded zero symbols. Start and end the carry
at0. The following twelve steps obey the actual scalar FIFO and every
integer carry transition. The rail order in the table is append0,
append1,read0,read1; k and N are the values before the step.

| j | k | N | Four rail bits | Next k | Next N |
|---:|---:|---:|:---:|---:|---:|
|0|0|30|1100|13|64|
|1|13|64|0001|0|21|
|2|0|21|1100|13|61|
|3|13|61|0010|-16|20|
|4|-16|20|0011|-39|6|
|5|-39|6|0000|-4|2|
|6|-4|2|0011|-35|0|
|7|-35|0|1000|0|27|
|8|0|27|0000|9|9|
|9|9|9|0000|12|3|
|10|12|3|0000|13|1|
|11|13|1|0001|0|0|

At each step read0+read1=N modulo3,

    N_next=floor(N/3)+27*(append0+append1),
    3k_next=k+27+8append0+4append1-88read0-40read1.

The append blocks are20,20,00,01,00,00; the read blocks are01,01,20,20,
00,01. Thus the first uncoded20 block is followed by actual consumption
of uncoded blocks, yet the run ends with both queue and carry zero.
Leaving the intended boundary-state set temporarily does not invalidate
the arithmetic source: it certifies the entire carry graph. In particular
this example refutes delayed rejection as an automatic property of this
fixed candidate, not merely exact equality of its local block graph.

## 2. Positive extension to the audited arithmetic architecture

Use the reviewed65 FIFO with ordinary input x=15, so I=2x. Let t=12,
q=3^12=531441, H=(q-1)/2, and let each Fi be H plus its rail word
from the table. All fields and all slacks q-Fi are positive. The first
append rail has units digit1. The FIFO identity gives automatic even
packing parity, and every supplied field is a native positive ternary
word. Set beta=W-I=51 and L=q/W=6561.

The exact65 theorem therefore supplies all remaining strictly positive
Pell witnesses. This is a parametric extension via an established
equivalence theorem, not numerical materialization of the enormous
auxiliary coordinates. The checker audits the literal65 source, the
positive outer values, the native valuation, and the packing parity.

To obtain integer fixed numerals in the general75 source, double every
carry coefficient and carry state. In append-first order the weights
are(16,8,-176,-80), h=54, cs=cf=0. The paid constants are
lambda=143 and delta=0, so its extra equality is exactly

    16F0+8F1-176F2-80F3+143(q-1)=0.

The table satisfies it, as checked both locally and globally. The
literal general75 schedule is audited too. The zero fixed constant
can simplify a particular specialized schedule; no new minimal count
is claimed here. The key fact is that all geometry, positive-domain,
ordinary-input, origin, transport and endpoint obligations of the
reviewed source are met while code typing fails.

Numerically its scalar sums are A=2207 and D=178797, so A+D=181004<q,
with slack350437. Also I=6*5. These additional facts are recorded for
comparison with pending input and bound refinements; this proof invokes
only the already reviewed65 interface.

## 3. Rail identifications do not repair this fixed block compiler

For each of the six desired Rule110 block transitions, exhaustive
two-step evaluation of its sixteen possible Boolean labels gives exactly
one rail path. In append0,append1,read0,read1 order, the corresponding
four rail-word vectors are

    A/0 ->0/A: (0,3,0,3),
    A/1 ->1/B: (0,1,0,1),
    B/0 ->1/A: (0,1,0,3),
    B/1 ->1/C: (1,0,1,0),
    C/0 ->1/A: (1,0,0,3),
    C/1 ->0/C: (0,3,1,0).

The matrix of these rows with an appended constant1 has rank5. The
receipt gives a nonzero5-by5 minor. Hence no nontrivial fixed affine
identity on the four two-trit rail words holds for every desired edge.
In particular no pair of rails can be identified, fixed to a constant
word, or required to be complementary while preserving all six rows.
For complements the two-trit Boolean words would sum to4, the ternary11
word. The checker tests each pair separately as well.

This is a criterion for fixed block identities and literal rail sharing.
It is not an obstruction to another global equation with state-dependent
carries; the existing weighted controller is itself such an equation.
Nor does it exclude a redesigned state coding or a more elaborate
bounded-cost code filter. No complete filter using at most three added
operations has been established here.

## 4. Loading and cleanup remain separate obligations

An everywhere01/10 read filter would also constrain the ordinary input:
for the65 interface, x=1 has I=2 and its first read trit is necessarily2.
The stronger counterexample above avoids relying on that simple mismatch
by beginning with an already coded queue.

For an aligned positive two-trit queue width, m is positive and even.
Empty final queue forces the last m scalar append trits to be zero,
including a full final00 block. A permanent01/10 append filter therefore
cannot also implement cleanup. A prospective middle-region filter needs
explicit prefix and suffix handling or a different code; these are not
free consequences of the current transport equations.

The [checker](input_bridge_rule110_code_typing.py) replays the exact
table and symbolic source audit, then compares its
[receipt](input_bridge_rule110_code_typing.json). It does not rerun the
large historical suite. Independent proof/source/default review passed,
including the complete accepted run and the positive extension scope.
