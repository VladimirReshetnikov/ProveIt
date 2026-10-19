# Transfer-plus-one source replacement for K230

This note proves the mathematical source transformation in `verification/build_h229.py`.
It does not assert a Rocq theorem for the new229-state machine. The inputK230
Rocq development supplies the original logical calibration; the new source and
literal runtime require the separately stated transformations and certificates.

## Exact closed programs

Write `D6` for a decrement-and-test on logical register6, `I5` for an increment
of logical register5, and `C2` for the second-enclosing-continue instruction.
The old source subtree has leaves

```
00  CD6
010 CI5
011 CC2
1   CI5
```

The replacement has leaves

```
0  CI5
10 CD6
11 CC2
```

Both programs are closed: a run can only exit through normal fallthrough;
no break or continue escapes the subtree, and neither subtree contains halt.
Both terminate for every natural register file. If their entry values are
`R5=a` and `R6=b`, their unique exit values are

```
R5=a+b+1, R6=0,
```

with every other register unchanged.

For the old program, each successful decrement decreasesR6 byone and immediately
incrementsR5 byone; the continue repeats this loop. After exactlyb successful
iterations, the zero test exits the loop and the final increment addsone.
For the replacement, the initial increment addsone, and each successful
decrement returns through the continue to an additional increment. There are
exactlyb successful decrements andb+1 increments. Both arguments are formal
inductions onb and both runs contain exactly3b+2 source-instruction executions.

## Context theorem

A complete subtree of this structured binary program has a single entry and a
normal fallthrough exit. External structured break/continue instructions cannot
enter a proper interior point of that subtree: such targets are ancestor
boundaries of their own source positions. Therefore two closed, terminating
subprograms with the same register-file input/output function are interchangeable
in every structured source context. Relate configurations outside the four
replacement sites by their common contextual positions and equal registers;
relate entry and exit configurations at each replacement by the identity on
registers. The local induction above supplies the finite positive blocks between
these synchronization points. Neither replacement contains halt, so the
resulting complete programs have equivalent halting behavior for every initial
natural register file.

The argument concerns source registers only. Increment instructions also append
spare tape blocks in the binary interpreter, but those spare values are excluded
from the logical register semantics and the universal runtime theorem accepts
arbitrary finite nonempty spare tails. In fact both replacement programs execute
the sameb+1 increments, so even the number of appended spare blocks agrees.

## Exact K230 instances

The old pattern occurs at exactlyfour pairwise disjoint prefixes:

```
111010010010111111000011
11101001001011111110011
1110100101100011
111110011
```

The source changes from5125 to5121 leaves, retains212 distinct DAGnodes,
maximum depth40, and maximum consecutive-zero run6. Only the shared decoder
state121 changes in the unfurled230-state literal table:

```
121/0: 0 R31 -> 0 R63
121/1: 1 R63 -> 1 R13
```

A separate all-tape block proof then deletes state79 into63. All old incoming
state79 edges are retargeted to63; the only such edge is70/1. The new63 rows are
`0 L123` and `1 L30`. The source replacement, binary runtime theorem, exact blank
startup, and all-tape fold theorem must be composed explicitly. A source proof
alone does not validate modified binary decoder rows.
