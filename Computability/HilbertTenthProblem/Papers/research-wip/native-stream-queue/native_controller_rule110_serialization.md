# Two-step Rule110 carry experiments with exact escape audits

Two scalar trits per bit evade the
[direct one-step algebraic obstruction](native_controller_rule110_affine_synthesis.md).
One small carry controller realizes the Rule110 scan relation exactly
**conditional on both streams using the two-trit code**. That code is
not enforced by the existing native Boolean-field typing, and an explicit
uncoded output is accepted without it. A larger example also shows why
checking only edges between three selected boundary carries is insufficient:
an entirely coded path can leave those carries and return with a wrong
transduction.

These are controller relations, not complete FIFO counterexamples or
certificates. No ordinary-input loader, row alignment, accepting simulation
or paid code filter is supplied. The complete universal bound remains76.

## 1. Exact two-step interface and finite verification

Both examples encode logical0 by low-first trits(0,1), and logical1 by
(1,0). Their integer block values are3 and1. Boolean rail words have
values0,1,3,4. A scalar block value is the sum of its two rail words;
the representation of each trit1 remains nonunique.

For read rail block values D0,D1 and append values A0,A1, the two-step
carry equation is

    9 c_next = c_current + 4h + u0*D0+u1*D1+v0*A0+v1*A1.    (1)

The [checker](native_controller_rule110_serialization.py) enumerates all
rail decompositions of each permitted block. Whenever (1) has an integer
target, its reduction modulo3 proves the first individual step integral;
the checker also reconstructs and verifies both microsteps directly.

Starting at carry0, it computes the entire reachable block-boundary
graph, then the subgraph of carries from which0 is reachable. This is
an exact finite procedure, not a chosen time cutoff: the invariant bound

    |c| <= |h|+|u0|+|u1|+|v0|+|v1|

contains every individual carry reached from0. Closing the finite graph
therefore covers paths of arbitrary length. Valid input blocks are always
assumed. Two separate graphs allow either only valid output blocks or
every output block with ternary value0 through8.

The target logical controller has the six transitions in Section1 of the
one-step note. A means the last input bit is0, B remembers01, and C
remembers11. Paths in this note start and end at A.

## 2. An exact conditional coded transducer

Take

    (A,B,C)=(0,8,4),  (u0,u1)=(-88,-40),
    (v0,v1)=(8,4),    h=27.

When both input and output blocks are restricted to the code, the entire
reachable carry set is {-16,0,4,8}. Carry-16 cannot return to0. Removing
it leaves exactly the six Rule110 transitions, with no other edges.
Thus all accepted coded input/output pairs, of every finite length,
are precisely the Rule110 scan paths starting and ending in A. This
statement permits extra carries before trimming; it does not assume in
advance that every boundary is one of A,B,C.

The native four-field typing does not impose this block code. Without
the output restriction, the reachable and returnable set becomes
{-16,-12,0,4,8,12}. There is already a wrong one-block path:

    read rails (D0,D1)=(0,3), append rails (A0,A1)=(1,1),
    individual carries 0 -> 13 -> 0.

Its input is logical0, but its output trits are(2,0), which is not a
codeword. Equation(1) is exact because

    4*27 - 40*3 + 8 + 4 = 0.

Thus the conditional transducer is a concrete target for a future paid
block filter. It is not a complete controller implementation today.

There is a separate endpoint obstruction to imposing this filter on every
append block of a whole run: each codeword contains a nonzero trit,
whereas an empty final FIFO requires the last m appended trits to be
zero. In particular a permanently coded output stream cannot supply
arbitrarily wide empty-queue computations. A future compiler needs a
cleanup phase, a different code with a zero word, or another explicitly
proved terminal interface. The return-to-A transducer acceptance used
here alone does not implement empty-queue acceptance.

## 3. A boundary subgraph with a fully coded false return

Now take

    (A,B,C)=(0,456,480), (u0,u1)=(-2288,-2280),
    (v0,v1)=(-12,228),  h=1539.

Among edges with both endpoints in {A,B,C}, the six desired transitions
are exact, even allowing every possible output block. Nonetheless the
whole graph contains a path with input/output bits

    input:          100011010
    actual output:  101000111
    Rule110 output: 110011111.

Every input and output block uses the stated code. The boundary carry
path is

    0 -> 456 -> 48 -> -48 -> -88 -> 416 -> 552 -> 8 -> 456 -> 0.

The receipt gives the four rail words and both individual carries at
every block. The path starts and ends in A, so merely checking the
initial and terminal controller state does not exclude it.

The full graph over coded block pairs has27 reachable carries, of which
17 can return to A. Allowing arbitrary output blocks gives88 reachable
and58 returnable carries. Thus this candidate fails even the conditional
typed-block transducer relation that the smaller example satisfies.

This is a false accepting **transduction**, not an exhibited false full
FIFO witness: the input and output strings above have not been required
to satisfy a queue delay or the ordinary-input equation. Its purpose is
to refute the inference from an exact chosen boundary subgraph to an
exact controller relation.

## 4. Evidence boundary

The [receipt](native_controller_rule110_serialization.json) records both
complete finite graphs, their reverse-reachability trims, the exact
six-edge comparisons and the two explicit counterexamples. Run
`python native_controller_rule110_serialization.py` to reproduce it.
No exhaustive claim is made about other coefficient choices or block
codes. Independent full proof, source, and default-replay review passed.
