# A conditional Rule110 carry controller with a zero codeword

The two-step code

    logical0 -> low-first trits(0,0),
    logical1 -> low-first trits(1,2)

has integer block values0 and7. With both read and append streams
restricted to this code, the carry controller

    3c_next=c_current-28*d0+56*d1-5*a0+2*a1               (1)

realizes exactly the three-state Rule110 scan transducer. It has initial
and final carry A=0, and the other state codes are B=14,C=7. Its full
reachable graph over coded block pairs is exactly these three states,
with the six desired edges and no additional states.

This is a conditional controller theorem, not a new complete certificate.
Native Boolean typing does not impose the00/12 block code. The unfiltered
output relation has explicit wrong accepting paths. Ordinary-input
normalization, row boundaries, and a complete accepting simulation remain
unprovided. The complete universal bound remains76.

## 1. Exact graph and the positive conditional result

For a two-trit block, the possible Boolean rail words have values0,1,3,4.
Scalar block0 has rails(0,0), whereas scalar block7 has rails(3,4) or
(4,3). The two-step equation is

    9c_next=c_current-28*D0+56*D1-5*A0+2*A1.             (2)

The complete coded graph is the following. Rail entries are word values,
not individual digits.

| Source | Read bit | Write bit | Target | Read rails | Append rails |
| --- | ---: | ---: | --- | --- | --- |
| A=0 | 0 | 0 | A=0 | (0,0) | (0,0) |
| A=0 | 1 | 1 | B=14 | (3,4) | (4,3) |
| B=14 | 0 | 1 | A=0 | (0,0) | (4,3) |
| B=14 | 1 | 1 | C=7 | (4,3) | (3,4) |
| C=7 | 0 | 1 | A=0 | (0,0) | (3,4) |
| C=7 | 1 | 0 | C=7 | (4,3) | (0,0) |

These are precisely the minimal Rule110 scan transitions specified in
[the direct-embedding note](native_controller_rule110_affine_synthesis.md).
Exhausting the two rail choices of each nonzero coded block proves the
table. Reduction of(2) modulo3 and then division by3 verifies the two
individual integral carry steps. The [checker](native_controller_rule110_zero_code.py)
does both computations independently and closes the entire finite graph.

The zero codeword has a useful difference from the earlier01/10 proposal:
the A/read0/write0 transition stays at carry0 while appending zeros.
Thus a coded zero suffix is compatible with an empty final queue. This
does not itself prove that every desired computation can be arranged to
reach such a suffix; it removes the earlier immediate incompatibility
between a permanently nonzero code and zero queue contents.

The opposite signs of the read weights also avoid the same-strict-sign,
zero-terminal bounded-input lemma. This is only avoidance of that
necessary obstruction, not evidence of a full universality reduction.

## 2. Why the block restriction is still essential

Allow every append block, while retaining coded input blocks. The entire
reachable graph then has16 carries, all of which can return to A. In
particular there is a two-block path with scalar input00,00 and outputs
(2,1),(1,0), both uncoded:

    first read rails(0,0), append rails(4,1): 0 -> -1 -> -2;
    next  read rails(0,0), append rails(0,1): -2 -> 0 -> 0.

This is a false return-to-A transduction on two logical zeros. It is not
asserted to satisfy the full FIFO delay identity. It proves that removing
the block restriction changes the controller relation, even with the
same initial and final carry.

The finite graph check is unbounded in path length. Every individual
carry reached from0 satisfies

    |c| <= 28+56+5+2=91,

and all integral outgoing transitions for the permitted blocks are
enumerated until closure. No longer path can leave that computed
reachable graph.

## 3. Conditional source cost and outstanding interfaces

Let Fi=H plus the corresponding native Boolean rail, and Q=2H=q-1 be
the existing width mask. Doubling the four weights gives the exact
controller identity

    -56*Fread0+112*Fread1-10*Fappend0+4*Fappend1-25*Q=0.   (3)

The H terms cancel because the doubled coefficient sum is50. Equation(3)
is equivalent to the zero-initial, zero-terminal global form of(1).
Group the positive and negative terms on the two sides of a free equality:

    112Fread1+4Fappend1 = 56Fread0+10Fappend0+25Q.

The five fixed scalar products and three additions cost8 operations.
The checker audits this literal schedule and its independent polynomial.
There is no final constant addition because both endpoints are0. Doubling
the controller gives a bijection of integral paths: the new carries stay
even from their zero start, so division by2 recovers the old ones.

This ledger includes only the controller equation. A block filter must
still be supplied and paid. The first append rail has units digit1 on
the A/read1/write1 route, so that route can meet the retained field
origin condition. The A/read0/write0 route has first append digit0.
Consequently raw input6x or2x cannot simply be declared to begin as a
coded computation: a suitable preamble and input normalization need a
separate soundness and completeness argument.

Nor does the local Rule110 scan table establish queue row alignment,
the desired initial controller state on subsequent rows, or an accepting
simulation from ordinary positive input. Those are distinct remaining
obligations after code typing. No complete universal count is claimed.

The [receipt](native_controller_rule110_zero_code.json) records both
complete graphs, the exact table, the uncoded counterexample, and the
coefficient cancellation in(3). Run the checker without `--write` for a
fresh comparison. Independent full proof, source, and default-replay review passed.
