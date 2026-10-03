# A precise prime-power input theorem for the three-mass route

The source input-encoding gap can be closed at theorem level. For every recursively enumerable set S of positive integers, one can effectively construct a finite **separated deterministic reversible two-counter machine** R_S, with no incoming instruction at its initial state and no outgoing instruction at its designated accepting state, such that

```
R_S started at (2^(96x),0) reaches its accepting state  iff  x belongs to S.
```

This is a precise prime-power convention, not an assertion about the unary two-counter input `(x,0)`. Together with the separately paid two-layer exponent interface and the reviewed source divide96 prefix, it provides ordinary-input universality for an effectively compiled family of three-mass sources. No numerical universal table, universal arithmetic count, or gigantic native Pell witness is supplied here.

There is also an exact fixed-interpreter input recipe, proved below: one fixed reversible source can use `(3^e*2^(96x),0)` for program index e. Its construction is effective, but its complete finite table and resulting arithmetic source have not been expanded and measured in this packet.

## 1. The primary theorem specifies the input

The primary source is Kenichi Morita, *Universality of a reversible two-counter machine*, Theoretical Computer Science168(1996),303–320, [DOI](https://doi.org/10.1016/S0304-3975(96)00081-3). A [copy of the primary paper](https://www.mobt3ath.com/uplode/book/book-94727.pdf?download=1) was downloaded and read. Its PDF SHA256 is `81677dd609d5b2c111c83fc5768382dbc14b54b1bf212a0b3fe828aca1b6c999`. The displayed relations on printed pages308 and313 were also checked visually against the PDF.

Theorem3.1, p308, converts a deterministic k-counter machine into a reversible `(k+2)`-counter machine, preserving its original initial counter tuple and initializing the two added counters to zero. A final history counter may be nonzero; the other added counter is zero.

Theorem4.1, p313, converts a reversible k-counter machine to two counters using the exact encoding

```
(q,m1,...,mk)  ↦  (q, product_i p_i^mi, 0),
p1=2, p2=3, p3=5,... .
```

Both statements quantify all initial and final natural tuples. The latter proof gives primitive increment, decrement and test implementations on pp314–316. These precise statements strengthen what was available from the earlier Morita–Imai2001 existence citation; they do not require guessing an effective encoder.

## 2. An ordinary unary recognizer before reversible compression

Here is an explicit finite-counter initialization argument, independent of an unspecified Turing-machine input encoding. Fix a deterministic Turing machine recognizing the unary language `{1^x:x∈S}`. Such a machine exists by the definition of recursive enumerability and a computable conversion between unary and the chosen usual integer representation.

Use a fixed base b larger than every tape-symbol code, with blank0 and unary symbol1. A stack word has its top symbol as its least significant base-b digit. Zero represents an empty stack followed by blanks. The machine uses two stack counters L,R and one scratch counter W, which is zero at every stack-operation boundary. The current tape symbol and Turing control state are finite control.

The following operations are literal finite programs in unit increment/decrement and zero/positive tests:

- `push(A,d)`: while A is positive, decrement A and increment W exactly b times; then transfer W back to A by paired decrement/increment steps; finally increment A exactly d times. It maps `(A,W)` to `(bA+d,0)`.
- `pop(A)`: consume A one unit at a time, keeping a residue in `{0,...,b−1}` in finite control and incrementing W whenever the residue wraps from b−1 to0. Transfer W back to A. It returns the residue in control and maps A to `floor(A/b)`, leaving W zero.

Both descriptions have finite instruction tables because b and the symbol codes are fixed. Pushing a blank onto an all-blank stack leaves zero, which is the same infinite blank tail; no tape information is lost by that convention. A right Turing move pushes the written symbol onto L and pops R; a left move does the opposite. A stationary move changes only the finite-control symbol. All simulated steps preserve the zero-scratch boundary.

Start three counters at `(x,0,0)`. While the first is positive, decrement it and push1 onto the second, using the third as scratch. At completion their contents are

```
(0, 1+b+...+b^(x−1), 0).
```

The first counter can now be L, the second R, and the third W. Popping R initializes the head symbol. Thus an explicit deterministic three-counter program recognizes S from `(x,0,0)`, without any external tape-code input. Empty x=0 is handled by the same macros, although the composed Diophantine interface below uses x>0. A fresh initial no-op label gives no incoming initial instruction. Only the designated accepting Turing state is routed to the designated final label; a rejecting or undefined nonaccepting computation is not an acceptance.

## 3. The scale96 is removed before the prime encoding

Prepend the reviewed finite divide96 prefix at the **multi-counter** level. It acts on the first counter and a zero scratch counter. Its block loop consumes96 units from the first counter and adds one to the scratch counter. After exact exhaustion, a transfer loop returns the quotient to the first counter and clears the scratch.

At a division-loop state Li, for i=0,...,95, the invariant is

```
C0 + 96*Cscratch + i = 96x.
```

On this input slice every block completes. The transfer loop then preserves `C0+Cscratch=x`, finishing at `(x,0)` on these two counters. Other counters are unchanged. The literal prefix has201 states and202 instructions and takes `198x+4` source instructions on `(96x,0)`. Missing zero cases at intermediate residues reject malformed nonmultiples; they never affect the stated slice. The [earlier exponential bridge](three_mass_exponential_input_bridge.md) already proves its separated reversible syntax and inverse. The checker here reconstructs it independently and also uses a nonzero untouched program counter to verify the scratch boundary.

Apply this prefix before the three-counter recognizer in Section2. The resulting deterministic machine starts at `(96x,0,0)`, accepts exactly x∈S, and returns every preprocessing scratch to zero before the recognizer starts. Its initial label has no incoming instruction.

Now apply Morita's Theorem3.1 and then Theorem4.1. The first construction initializes its extra history/work counters to zero. The second therefore has initial prime code

```
2^(96x) * 3^0 * 5^0 * 7^0 * 11^0 = 2^(96x),
```

and its other physical counter is zero. This proves the first displayed theorem.

## 4. Why reaching the final label is a genuine simulated halt

The theorem statements compare encoded initial and final configurations. For this application one also needs to know that reaching the final control label cannot produce a spurious nonencoded output.

The boundary invariant is: at every original source-state label, the first simulator counter is a positive product of the designated primes with natural exponents, and the second is zero. Each primitive macro has fresh internal labels. Multiplication by p, exact division by p and a divisibility test followed by restoration preserve that invariant on valid source transitions. A decrement on a zero simulated counter cannot finish its division macro. A missing test branch cannot reach another original-state label. All active arithmetic loops on a valid finite input terminate, and they return the working counter to zero.

Induction from the encoded start therefore identifies **every** visit to an original source label with its simulated natural counter tuple. In particular, visiting the designated final label has a proper encoded output. The history simulation has the analogous original-state boundary: original counters, a natural history, and zero work. Fresh internal states cannot themselves be the accepting label. Hence halting equivalence follows, not merely equivalence restricted to a preselected output tuple.

The no-incoming initial-state property also transfers through the constructions: added macro states are fresh, and transitions into old labels arise only where the original source had incoming transitions. The starting deterministic recognizer was chosen with no such incoming transition. Deleting outgoing instructions from the designated final label, if necessary, preserves reversibility and makes acceptance terminal. These conditions match the three-mass compiler's separated source contract.

The [checker](three_mass_prime_power_input_theorem.py) implements a source-level prime macro compiler and checks its exact separated syntax in both directions. The primary seven-instruction three-counter duplication example compiles to93 primitive instructions; the checker follows all original-state boundaries, not just the final arithmetic answer. This is a finite example supporting the invariant, not a universal table.

## 5. What two paid exponent layers buy

Use positive ordinary x and impose both exponent components' positive output projections separately:

```
Q1 = 2^(96x),
N0 = 2^(96 Q1).
```

The initial three-mass payload N0 has valuations `(96 Q1,0)`. Attach the finite reversible divide96 prefix at the **physical source-counter** level, followed by the R_S just constructed. The prefix reaches `(Q1,0)=(2^(96x),0)`, exactly the input required by R_S. Therefore the composed three-mass source accepts this externally loaded input exactly when x∈S.

There are two different divide96 occurrences: one is inside the multi-counter machine before reversible prime compression, removing96 from its virtual ordinary input; the other is a physical two-counter prefix removing the outer96 from the mass valuation. Neither is a free algebraic decoding operation. Both have finite source instructions, and compiling the resulting source requires its actual table. The physical clock includes both prefixes and all other source instructions actually executed after initialization. The external work of preparing the initial mass is not part of that clock.

The [double-exponential arithmetic bridge](three_mass_double_exponential_input.md) pays the two exponent relations and the unbounded fixed-source history. Its illustrative circuit costs do not include an unexpanded universal source. The two exponent unit constraints must each equal+1; accepting only an unchecked product of the two units would not be the same theorem. Positive extensions exist separately for both layers on the stated inputs, while the source history witnesses carry their existing existential multiplicities.

## 6. Optional fixed-interpreter program recipe

A fixed universal Turing recognizer can instead receive the unary word `1^x 2 1^e`, with e the index of a recursively enumerable language. Five counters suffice for an explicit initialization: counters0 and1 start at x and e; counter2 is an empty left stack, counter3 the right stack, and counter4 zero scratch. Push e ones, the separator2, and then x ones onto the right stack. Its least-significant-first word is precisely `1^x 2 1^e`. Both input counters are consumed to zero; the two stacks and scratch then simulate the fixed Turing recognizer.

Before this loader, divide96 on counters0 and2. It takes `(96x,e,0,0,0)` to `(x,e,0,0,0)` and preserves e. Applying the two Morita constructions to this **one fixed** deterministic five-counter program yields one fixed reversible two-counter machine U whose prime-coded input is

```
(2^(96x)*3^e, 0).
```

This is an existence-plus-effective-construction theorem for a fixed interpreter; it is not a displayed numerical universal instruction table. Its valid fixed-program numeral recipe is `C=3^e`.

For that slice, let the second paid exponent receive `C*Q1`:

```
N0 = 2^(96*C*Q1),       Q1=2^(96x),       C=3^e.
```

The external source divide96 produces counter value `C*Q1`, exactly the prime code of `(96x,e,0,0,0,0,0)` before U's two-counter compression. When C is a fixed program numeral, the existing exponent row `r=48*z` with `z=C*Q1` can be emitted as `r=(48C)*Q1`: the coefficient48C is precomputed for the fixed slice. This uses one multiplication rather than treating a variable product as free. If C itself is an ordinary variable, that fixed-coefficient argument does not apply.

Thus the ordinary-input recipe is explicit. Remaining work for a numerical universal Diophantine bound is to expand one actual universal source and both prefixes, fix all instruction/state codes, feed that exact table through the unbounded-history compiler, and charge and validate the entire final source. No count for one of the small example machines can be transferred to U.

## 7. Reproducible evidence and exact limits

The [receipt](three_mass_prime_power_input_theorem.json) records a standard-library source-level checker, not a Diophantine circuit emitter. It checks:

- 1,920 prime macro cases for primes2,3,5,7,11 and both one-sided and paired tests, with1,359 successful exact inverse runs;
- Five full prime-encoded simulations and65 individual original-state boundaries in the93-instruction example;
- 1,005 divide-prefix cases, including malformed nonmultiples and a preserved nonzero program counter, with413 inverse runs;
- 820 literal stack-push cases,505 stack-pop cases,35 unary loads,36 paired unary loads and12 composed divide96/paired-loader initializations;
- 20 exact symbolic-interface instances of the prime code for `(96x,e,0,...)`, without materializing the doubly exponential physical mass.

These finite cases do not establish recursive enumerability or universal simulation; the general construction and primary theorems above do. No full universal source table, giant physical trajectory, or complete positive native Pell tuple is materialized. No unary two-counter impossibility claim is made or inferred from a Schroeppel abstract.

```sh
python3 three_mass_prime_power_input_theorem.py \
  --expect three_mass_prime_power_input_theorem.json
```

`--output PATH` writes a fresh receipt. Optional `--paper PATH` additionally authenticates the reviewed PDF bytes; without it replay checks the mathematics without downloading the paper. The recorded PDF hash is provenance, not a claim that the file was fetched on every replay. No historical Python modules are imported and no repository files are written. Optimized `-O` execution is rejected, and receipt comparison is recursively type-sensitive.
