# Chronological toggle tapes: 105 certificate operations and a 158-operation polynomial

A single prescribed native AND certifies arbitrarily many chronological
binary toggles, with a positive one-hot head and the current read in every
row. The complete certificate costs **105=48M+57A**, with **18 comparisons**
and **28 positive existential witnesses**. Its sum-of-squares polynomial
costs **158=66M+92A** and has total degree **at most124**. The two positive
parameters are the initial and final tape words plus1.

The [source](langton_ant_packed_toggle_tape.py) and
[receipt](langton_ant_packed_toggle_tape.json) count all native arithmetic,
positive adapters, radix typing, bounds and temporal transport. The new
mixed-scale observation types both radices through positive factors of
one dyadic native scale. It removes the dedicated radix-test lanes used
in the [packed Wang tape](wang_b_packed_tape.md).

This is a supplied-history component, not a complete Langton-ant history.
Head motion and turns are absent. Indeed, Section5 proves that its
existential endpoint relation is **all** pairs of nonnegative integers.
It therefore gives no universal bound and does not replace the earlier
[174-operation bounded ant history](../../1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md),
which also certifies planar geometry and heading.

## 1. Primary universality scope and the new arithmetic lemma

[Gajardo, Moreira and Goles, *Complexity of Langton's Ant*, Sections3–4](https://arxiv.org/pdf/nlin/0306022)
separate finite-support circuit P-hardness from universal simulation on
an infinite, finitely described background. Their universality conclusion
does not establish universality from finite-support initial ant tapes.
[Maldonado, Gajardo, Hellouin de Menibus and Moreira, *Nontrivial Turmites are Turing-universal*, Theorems2.1 and3.1](https://arxiv.org/pdf/1702.05547)
provide a periodic hardware background with a finite input perturbation.
The finite initial configuration in Theorem3.1 belongs to the simulated
one-dimensional machine or cellular automaton. The turmite's hardware is
infinite. Its Section4 P-completeness concerns prediction with a time
bound. None of these statements pays an ordinary-integer input map,
a variable finite-window background generator or a simulated-halting
observable in the arithmetic source below.

Here is the arithmetic improvement, independently of universality.
Suppose positive integers B and P and nonnegative lane coefficients
`a_i,b_i,z_i<P` have already been bounded. For fixed positive a at least
the number L of lanes, use the complete prescribed-scale AND at

    Scale=B*P^a,
    A=sum_(i<L) a_i P^i,
    M=sum_(i<L) b_i P^i,
    Z=sum_(i<L) z_i P^i.                            (1)

The native theorem makes Scale a power of two. Every positive divisor
of a power of two is dyadic, so both B and P are powers of two. The
lane bounds give A,M,Z<P^L<=Scale. Splitting the now binary-aligned
P-lanes recovers every `a_i AND b_i=z_i`. Conversely, dyadic B,P and
these lane relations satisfy the complete native predicate and admit its
full positive auxiliary extension. All multiplications in(1), including
the factor B, must be paid. This is not a promise that arbitrary
unbounded or signed coefficients concatenate correctly.

The packet uses L=a=4. It needs no reserved top lanes or separate
comparison for `B AND(B-1)=0`, even when the duration is1 and B=P.

## 2. Positive coordinates and one shared native AND

Write the positive endpoint parameters as T0hat,Tthat. Besides the22
positive auxiliaries of [prescribed AND64](native_binary_masked_selection63.md),
supply exactly six positive coordinates

    height_slack, global_bound, J, T_hat, G_hat, C_hat.

Decode T=T_hat-1, G=G_hat-1 and C=C_hat-1, and compute

    D=T0hat+Tthat+height_slack,
    B=4D, Pminus=(B-1)J, P=Pminus+1,
    H=G+J, R=(D-1)J.                               (2)

Before any equation D>=3, B>=12, J>=1 and P>=B. All words in(2)
are nonnegative, and H is positive. Pay the global comparison

    J+T_hat+G_hat+C_hat+global_bound=P.             (3)

It makes T,G,C and H strictly smaller than P. Also
`0<=R<P`, directly from D-1<B-1 and(2). These bounds precede native
bit typing. They are not inferred from an assumed digit interpretation.

The four scalar AND lanes are:

| P-lane | First input | Second input | Output |
|---:|---|---|---|
|0|H|G|0|
|1|T|H|C|
|2|T|R|T|
|3|G|R|G|

Thus the literal packed words and scale are

    A=H+PT+P²T+P³G,
    M=G+PH+P²R+P³R,
    Z=PC+P²T+P³G,
    Scale=B*P^4.                                   (4)

The source shares the common high suffix between A and Z; it does not
recompute it or treat it as a free expression. Native ports are
`16A+12,16M+10,16Z+8,16Scale`. They are strictly positive before any
equations, so the inherited prescribed-AND domain applies literally.

By Section1, B and P are powers of two. Since P=(B-1)J+1 and J>=1,
the elementary divisibility criterion for `2^b-1` gives

    P=B^t, J=1+B+...+B^(t-1), t>=1.                (5)

In detail, B=2^b and P=2^p with b,p>0, and B-1 divides P-1 iff b
 divides p. Also D=B/4 is dyadic. No separate duration or radix
predicate has been omitted.

## 3. Reads, head positivity and exact temporal transport

Use the canonical base-B digits of the bounded words. The two range
lanes give `0<=T_i,G_i<D`, because R consists of D-1 in every one of
the t radix cells. Hence H=G+J has digits H_i=G_i+1 with no carry,
and `1<=H_i<=D`. The first lane now gives

    H_i AND(H_i-1)=0,

so every H_i is a strictly positive power of two. This derivation rules
out zero rows hidden by borrowing between whole words. For example,
J=B+1, H=2B and G=B-1 obey `H AND G=0` but give a zero first head;
the range lane excludes their first G digit B-1.

The read lane gives C_i=T_i AND H_i. Thus C_i is either0 or H_i,
and the integer expression

    U_i=T_i+H_i-2C_i=T_i XOR H_i                  (6)

is nonnegative and smaller than2D<B. Consequently
`U=T+H-2C` is the carry-free packed word of the following tapes. This
expression may be negative on arbitrary off-zero input tuples; it is
never used as an untyped native port.

The final outer comparison is the positive-adapter form of

    B*U+T0=T+P*Tt,                                (7)
    left=B*(T+H-2C)+T0hat,
    right=T+P*Tthat-Pminus,  left=right.

Both endpoints T0=T0hat-1 and Tt=Tthat-1 lie below D by(2). Unique
base-B expansion in(7) therefore gives the initial tape, all adjacent
rows, and the final tape. Every zero decodes a nonempty sequence

    C_i=T_i AND H_i,
    H_i=2^(j_i)>0,
    T_(i+1)=T_i XOR H_i,  0<=i<t.                 (8)

The source simultaneously certifies the complete supplied histories;
it does not read every row from the final tape or merely record the
parity of the multiset of visited cells.

Conversely, take any finite nonempty sequence(8). Choose a dyadic D
strictly greater than all its tapes and heads and than T0hat+Tthat.
Set B=4D, P=B^t and J as in(5). Pack T_i,H_i-1,C_i to form T,G,C,
and add1 to each supplied hat. The height slack is positive. The global
slack is also positive: each of the three packed words is at most
`(D-1)J`, so

    P-J-T_hat-G_hat-C_hat >= (D+1)J-2 > 0.         (9)

All four lane relations and(7) hold. The inputs of(4) are less than
P^4 and hence less than the dyadic Scale=B*P^4. The full prescribed-AND
converse supplies all22 strictly positive native coordinates. This is
an existence proof of a complete positive Pell extension, not an
inference from small numerical fixtures.

## 4. Literal costs and degree scope

| Part | M | A | Total |
|---|---:|---:|---:|
| Positive adapters, D,B,P,H and range mask |3|9|12|
| Global bound |0|4|4|
| Toggle and chronological transport |2|6|8|
| Shared four-lane packing |7|7|14|
| Mixed scale B*P^4 |3|0|3|
| Complete prescribed AND |33|31|64|
| **Certificate** |**48**|**57**|**105**|
|18 residual squares and accumulation |18|35|53|
| **Single polynomial** |**66**|**92**|**158**|

There are18 comparisons: the two displayed outer comparisons and all16
native comparisons. The28 positive witnesses are the six outer
coordinates and22 native coordinates; duration and the bit width are
decoded from them. Fixed numerals are inputs, but every operation using
a fixed numeral is included.

Literal total-degree propagation through the whole source, assigning
degree1 to every parameter and witness, gives degree at most124 for
the final polynomial. This is a conservative upper bound and uses no
zero-set relation to simplify the degree. No exact-degree or optimality
claim is made.

## 5. Why this is not an ant recognizer

For any nonnegative endpoints a,b, flip once at each set bit of a XOR b.
This gives a finite path from a to b. If a=b, flip the lowest cell twice
to obtain a nonempty path. Section3 extends every such path positively.
Therefore the existential endpoint projection of this packet is exactly

    {(a+1,b+1): a,b>=0}.                            (10)

In particular, existentially choosing the final endpoint or all heads
cannot encode a nontrivial input language. The concrete path
`T=(0,1,0), H=(1,1)` passes this toggle relation but cannot be an ant
path: an ant moves to a neighboring cell after every flip, so two
successive source positions cannot coincide. This is a counterexample
to omitting motion, not to a complete ant or Diophantine compiler.

Every finite physical ant prefix can nevertheless be translated into a
sufficiently large finite rectangle and flattened injectively. Its board
words and powers-of-two head positions satisfy(8), including revisits
and either incoming turn color. This is a conditional component map:
placing that rectangle, preserving row boundaries, certifying both
coordinates and headings, and enforcing the color-dependent turn and
move remain additional obligations.

For a periodic-background simulation, a finite window suffices for any
particular finite prefix, but its initial board must be the correct
restriction of the same fixed background plus the prescribed input
perturbation. Supplying an arbitrary positive initial board parameter
does not establish that condition. Nor does it pay the map from an
ordinary positive integer to the simulation's finite perturbation or a
macro-pattern whose occurrence detects acceptance. The existing bounded
ant packet discusses such interfaces; this packet does not claim to
complete or improve their full combined cost. Current universal bounds
and the separate75/87 route are unchanged.

## 6. Reproducible evidence

```sh
python3 langton_ant_packed_toggle_tape.py
```

The source records512 independently assembled complete native-residual
and SOS identities,256 signed. It tests288 genuine outer toggle histories
through duration12, including24 duration-one cases and repeated visits.
A separate physical grid simulator generates72 ant prefixes, then checks
their finite-rectangle encoding against the complete outer relation.
The receipt gives their exact step total.

It also checks all1,024 endpoint pairs below32, the repeated-head
non-ant fixture, four zero-head borrow fixtures, and6,084 small mixed-scale
factor-typing instances. All genuine-path tests evaluate the full outer
relations and exact native AND interfaces. They do not materialize the
large canonical Pell witnesses. The proofs above, together with the
complete native theorem, supply arbitrary-integer soundness and the
positive converse.

Independent review: root completed full proof/source/fresh-default review
with no findings and separately checked the primary universality scope
in the cited 2003 Sections3–4 and 2017 Theorems2.1/3.1. Native completed
full proof/source/fresh-default review with no findings, including the
mixed-scale typing and the endpoint-projection obstruction. Native's own
literal executor additionally checked128 complete native-residual/SOS
identities,64 signed, and a separate physical set-of-cells simulation
packed64 ant prefixes totaling778 steps without calling this packet's
path or independent-evaluation helpers. The physical-prefix checks cover
the outer equalities, exact AND and scale bounds; they are not numerical
full Pell zeros. Both independent reviews confirm the105/158 ledger and
conservative degree bound124.
