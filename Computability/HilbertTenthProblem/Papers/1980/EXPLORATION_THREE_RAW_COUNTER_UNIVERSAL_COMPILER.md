# A fixed three-counter compiler with an ordinary integer input

The serial labelled-counter relation of
`EXPLORATION_SERIAL_RAW_COUNTER_COMPOSITION.md` is sufficient for a
universal Diophantine family. This note supplies the missing compilation
argument with its exact input and halting conventions. The resulting
alternative upper bound is **123 operations**, not an improvement of the
existing universal bound of 90. No extra arithmetic instruction is
silently charged to the input loader: the loader becomes part of the
fixed finite program encoded by the already counted ROM.

For every recursively enumerable set E of positive integers, choose a
Turing machine accepting precisely the usual finite binary expansions of
the members of E. The construction below produces a fixed finite labelled
graph G_E, independent of the query x, such that

    x belongs to E
      iff G_E has an admissible serial history from [2x,0,0] to [0,0,0].

The first sign is plus, each serial step updates one of the three
registers by exactly +1 or -1 in cyclic lane order, all register values
are nonnegative, and every source zero test is exact. These are exactly
the established 123-operation component's conventions. The fixed graph
can be compiled into its Sidon ROM constants. Every variable product and
every native mask field in that component remains counted; graph size
only changes fixed numeral values.

The proof is constructive and self-contained. Its maintained finite
compiler and regression are
`../verification/explore_three_raw_counter_compiler.py/.json`. Finite
tests corroborate the constructions but do not replace the termination
and equivalence arguments below.

## 1. Logical counter instructions and empty scratch

Use three logical counters A,B,C in the nonnegative integers, initially

    A=x, B=C=0.

Finite control permits increment, a zero-or-decrement instruction, and
a change of control location. A zero-or-decrement on register r has
two successors: if r=0, follow the zero edge without changing it;
otherwise decrement it once and follow the nonzero edge. A change of
control location changes no register. It can equally be inlined; its
explicit two-phase physical implementation is given in Section 5.

For any fixed integer b>=2 and digit d in {1,...,b-1}, a push on A
implements A:=bA+d while preserving B and finishing with C=0:

* While A is positive, decrement A and increment C exactly b times.
* Transfer C back to A one unit at a time, then increment A d times.

Here C is zero on entry. Both loops terminate because their decremented
counter strictly decreases. A fixed string of b or d increments is
finite control, not a variable-length instruction or a free arithmetic
operation in the Diophantine certificate. The analogous operation on B
preserves A.

A pop on A computes the quotient floor(A/b) in A and returns the
remainder in finite control, again preserving B and restoring C=0.
Start a finite-control remainder j at zero. Decrement A to zero,
cycling j through 0,...,b-1 and incrementing C once whenever j wraps
to zero. If the original value is n, the loop ends with C=floor(n/b)
and j=n modulo b. Transfer C back to A. A pop on B is symmetric.
All routines use only the stated counter instructions and the same
third scratch counter. In particular two stacks do not need two
additional scratch registers.

## 2. Load ordinary x, without assuming a prime-power input

Give every tape symbol a distinct positive code, including blank.
Let b be one larger than the number of tape symbols. The input symbols
0 and 1 have fixed positive codes code(0),code(1).

Starting from (A,B,C)=(x,0,0), repeat while A is nonzero:

    pop A in base 2, returning epsilon in {0,1};
    push code(epsilon) on B in base b.

The while test can use a zero-or-decrement followed, on its nonzero
branch, by one restoring increment before the pop. At every loop
boundary C=0. Each iteration changes the positive quotient to
floor(A/2), so the loop terminates after the number of binary digits of
x. It sees the binary digits from least to most significant. Pushing
them in that order leaves the most significant input digit on top of B.
On exit A=C=0, and popping B reads the standard binary input from left
to right. Positive x has a nonempty input without a leading zero.

This explicitly uses the raw numerical value x. There is no assumption
that the initial counter contains 2^x, a product of primes encoding x,
a digit-dilated numeral, or an input-dependent finite program. The
integer operation x+x in the Diophantine source supplies physical 2x;
the physical representation of logical counters is addressed below.

## 3. Two stacks simulate the tape, with one shared scratch counter

At a simulated machine-step boundary, A holds the stack strictly left
of the head, nearest cell on top. B holds the current head cell followed
by the cells to its right, again nearest cell on top. Counter C is zero.
Every stored stack digit is a positive symbol code. An empty stack has
value zero and popping it returns blank without changing any counter.
Thus absent cells are blank, while explicit blank digits may also be
stored. These two representations of unvisited blank tails have the
same tape semantics.

Pop B to obtain the scanned symbol, treating remainder zero from an
empty stack as blank. The machine state and symbol are finite control.
For a transition writing symbol tau and changing to state q':

* Move right: push tau on A. The remaining B already begins with the
  new head cell. Continue in state q'.
* Move left: pop A, obtaining sigma or blank when A is empty. Push tau
  on B, then push sigma on B. The latter is the new head cell, and A
  is the remaining left stack. Continue in state q'.
* Stay: push tau back on B and continue in state q'.

The routines of Section 1 preserve the other stack and restore C=0 at
every call boundary. Consequently each simulated Turing step terminates
after finitely many counter instructions and has exactly the intended
tape effect. Induction gives a faithful simulation for every finite
number of Turing steps. There is no global bound on tape size or counter
size: the same fixed program operates on arbitrarily large integers.

On a Turing acceptance, decrement A,B,C to zero and enter a unique
accepting halt location. This cleanup terminates. A rejecting halt is a
different location with no path to the accepting location. If the
Turing machine runs forever, its faithful simulation never reaches
acceptance; each individual macro terminates, so a stuck internal
routine cannot introduce a false accepting computation. We have proved

    TM accepts binary(x)
      iff the fixed logical three-counter program reaches its unique
          accepting halt from (x,0,0), with final values (0,0,0).

## 4. Why the graph may branch without introducing wrong computations

The numerical instruction semantics above are deterministic. A labelled
graph need not encode a conditional edge itself. Instead replace each
zero-or-decrement instruction by two possible entry branches, one with
an exact source-zero request and one with a decrement that fails by
underflow when the register is zero. Predecessor edges may choose either
entry. The arithmetic history relation admits exactly the numerically
valid branch, as the next section proves. Every other program location
has a single entry type.

Use separate accepting and rejecting halt vertices. Only the accepting
vertex is the fixed final endpoint of the Diophantine relation. The
accepting vertex's labels are never executed: labels belong to the
source of an edge, and the history ends on that vertex.

## 5. Two physical phases represent one logical instruction

At every logical instruction boundary, encode n_i as physical value
2n_i in each of the three registers. Each logical instruction is two
full banks of signed physical updates. A bank updates all three
registers once; its signs and zero requests are fixed labels.

For increment of register i:

    phase 1: every register +1;
    phase 2: register i +1, every other register -1.

The selected value rises by two and the others are unchanged. Every
intermediate value is nonnegative.

For the nonzero/decrement branch of register i:

    phase 1: register i -1, every other register +1;
    phase 2: every register -1.

If logical n_i>=1, its physical value is at least two, so both decrements
are legal and its final value is 2(n_i-1). If n_i=0 the first decrement
is illegal. Thus this branch cannot act as a false nonzero test.

For the zero branch of register i:

    phase 1: request source register i=0, then every register +1;
    phase 2: every register -1.

It is legal exactly when logical n_i=0 and changes no logical value.
A pure control-location change uses the same two phases without the
zero request. Inactive registers may be zero; their +1,-1 pair is
always legal. All instruction boundaries again have even physical
values. These local facts prove inductively that the graph has exactly
the logical counter computations, despite its syntactic branch choices.

Prefix the whole program by one all-plus bank and one all-minus bank.
This preserves the initial [2x,0,0] and ensures the first sign is plus,
even if the first logical instruction itself would start with a
decrement or conditional branch. This fixed prefix does not depend on x.

## 6. Serial expansion and the finite-width interface

Replace each physical bank vertex by three lane vertices, with phases
0,1,2. Lane i has the bank's sign for register i and its zero flag for
that register. Connect lane 0 to 1 and lane 1 to 2, and connect lane 2
to every permitted next bank's lane 0. The unique fixed initial vertex
is the prefix's lane 0. The fixed final vertex is the accepting halt at
phase 0. Every edge advances phase modulo three, so there are no
self-loops. Branch labels are tested at their lane's source; updates
of earlier lanes in the bank have not changed the tested register.

This is exactly the serial controller contract, whose numerical wiring
links the same register at positions separated by three blocks. Each
logical instruction uses six serial blocks. The fixed prefix does too.
All finite accepting paths therefore have a whole number of banks and
even bank duration. The component's independent soundness already
derives complete banks and accepts no partial-frame substitute.

For each finite accepting computation, choose its counter radix R as a
sufficiently large power of three. It can exceed both the compiled
program's fixed Rmin and three times every physical counter value in
the finite computation, and satisfy the strict input bound 2x<R.
Every numerical source then has the top-zero representation required
by the counter component. Increasing R does not change any instruction,
branch, label, or raw input. Thus the finite-width guards impose no
resource bound on the represented accepting computations.

Conversely every accepting positive Diophantine solution gives an exact
serial path, source-zero tests and nonnegative signed updates by the
123-operation theorem. Sections 4--6 decode that path into the fixed
logical counter execution. It must end at the accepting location, so
Sections 2--3 recover a Turing acceptance of binary(x).

## 7. Quantifiers and operation accounting

Given E, its semidecider fixes a finite tape alphabet and transition
table. Sections 1--6 produce a finite graph with fixed signs, zero flags,
initial vertex and final vertex. Compile this graph into the fixed
constants of the 123-operation theorem. They depend on E, never on x.
The result is a single fixed finite system with one positive input x
and 45 positive existential unknowns. Its straight-line certificate has
the established 56 products and 67 additions/subtractions, with 33 free
equality tests. In particular:

    for every recursively enumerable E subset of the positive integers,
    there is a fixed 123-operation system S_E such that, for every x>0,
    S_E has positive witnesses iff x belongs to E.

The variable x is doubled by the already counted operation x+x.
No additional input-conversion or compilation arithmetic is evaluated
outside the certificate. All unbounded work is witnessed by the finite
history whose geometry, masking, routing and Pell certificate have
already been counted. Choosing larger fixed program numerals neither
removes any of those operations nor adds free variable powers.

This is an alternate universal family above the existing bound of 90.
It makes future reductions of this raw-counter/controller architecture
meaningful for the original optimization objective, but does not claim
that those further reductions have already been achieved.
