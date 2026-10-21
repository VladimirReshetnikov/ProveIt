# Concrete zero-credit formalization and candidate comparison

## New checked result

`TagLowering.v` formalizes the existing ZC215 tag-lowering argument in the
Coq 8.18.0 standard library. The kernel-checked contribution is substantially
stronger than compiling the older generic `PrefixCredit.v`: the old prototype
assumed a lowering map, strict decrease and injectivity. The new file constructs
and proves all three for the actual nested Cantor command codec, proves an
executable parser correct, constructs every finite scheduler prefix, and derives
the count inequality without any candidate-specific premises.

The mathematical definitions are

\[
P(a,b)=\frac{(a+b)(a+b+1)}2+b,
\]

with fields DROP=[0], NIP=[1], MP(x)=[2,x], AX(c;x,y)=[c+3,y,x]. A last command
ends in residual zero. A nonempty continuation has residual one plus its raw
code. This distinction is essential: raw([DROP])=0 is a genuine candidate,
whereas a final DROP inside a longer word must be represented by positive
continuation residual one. No injectivity assertion includes the empty word.

`parse(n)` is the unique nonempty command word with raw code n. Its executable
implementation uses n+1 units of fuel. The residual for the next nonempty
continuation is at most n, so its raw index is strictly less than n. Theorems
`raw_parse` and `parse_raw` prove both inverse laws; `cp_closed` binds the
recursively defined triangular number to the usual closed Cantor formula.

For an occurrence (n,j) of NIP in parse(n), replace that command by DROP and
let m be the resulting raw code. The concrete map sends (n,j) to (m,j).
`lower_earlier` proves m<n. At the modified command, lowering the tag decreases
P(1,r) to P(0,r), a strict decrease of r+1; the enclosing Cantor pairs and
positive-continuation successors preserve the decrease. `lower_injective`
proves injectivity by the unique inverse operation at the same position.

Let `prefix(n,j)` contain every occurrence in parse(0),...,parse(n-1), followed
by the first j positions of parse(n). Let `pops`/`pushes` filter this list for
NIP/DROP. The two final, assumption-free statements are:

```coq
zero_credit n j :
  length (pops n j) <= length (pushes n j).

positive_credit_before_nip n j : Pop (n,j) ->
  S (length (pops n j)) <= length (pushes n j).
```

Every lowered occurrence is in a strictly earlier completed candidate, which
is why the second statement holds *before* an imminent pop. Neither theorem
assigns any positive stack credit to AX. The usual source stack invariant
can therefore start with no explicit protected heads over an arbitrary opaque
tail J. DROP adds a theorem head; NIP always has an earlier unmatched DROP to
pop; MP and AX need only preserve that lower bound. This removes the arithmetic
reserve/debt argument and any need to decode the initial stack tail J=5 as a
list of theorems.

This is **not** a new exact ZC215 binary-machine endpoint. Connecting its actual
source transition semantics and physical frame representation to this parser
and count model remains an integration obligation. Numerical-calculus/ZFC
calibration, command correctness, strong compiler completeness, primitive
runtime simulation and whole-tape initialization remain inherited obligations.
No unconditional nonhalting or 214-state result follows just from this file.

The new formalization is 393 source lines and 14,514 bytes. Five printed
assumption reports are closed under the global context. A fresh compiler and
recursive `coqchk` run are recorded in `evidence/receipt.json`; the portable
runner is:

```sh
python3 reproduce.py --output /tmp/zc215-credit-fresh
```

The proof uses only the standard library. It has no project dependency,
postulate, admitted proof, externally trusted oracle, or bounded natural-value
assumption.

## Which 215-state candidate is easiest?

Two different notions matter.

1. **The smallest additional proof after importing K215's existing endpoint.**
   The predecessor-marker family M124 and FM215 is the best inspected choice.
   Each changes four native rows, uses two immediate incoming-edge marker
   invariants, and replaces exactly two old cases by three-step blocks.
   Incoming packet5 already has standalone M124 proofs in both assistants;
   packet7 already has a standalone FM215 Lean proof. This task should credit
   those contributions and focus on adapting one to the repository tape
   semantics. The underlying K215 proof closure remains inherited.
2. **A cleaner source scheduler for a future independent proof.** ZC215 has the
   strongest demonstrated simplification: an exact injection replaces stack
   credit estimates, safely admits an opaque startup tail, and needs no AX
   credit. GC-ZC215 additionally simplifies generalization by using the command
   tag as binder, but requires its new conditional decoder merge. There is no
   measured full proof-size comparison establishing either as a smaller total
   formal development than K215.

| Candidate | New proof obligation | Assessment |
|---|---|---|
| M124 or FM215 | Two origin markers; two 3-step blocks; native/zipper endpoint adapter | Smallest clear incremental transfer |
| CM215 | Similar positive simulation with an extra history-sensitive marker case | Very close; existing Core bridge may make integration practically cheaper |
| ZC215 | Exact codec/prefix injection; scheduler/refill adapter; physical simulation | Best evidenced source-safety simplification |
| GC-ZC215 | ZC proof plus command-tag GEN and conditional decoder allocation | Clean command compiler, more changed layers |
| ST215 | Direct transfer command, protected-tail credit, compiler/backend adaptation | Fewer primitives, larger current proof delta |
| FT215 | Forced transfer before each candidate, debt-seven scheduler argument | One changed row does not mean a short proof |

## M124 and FM215 must not be conflated

They use the same two-marker design but are different literal graphs:

| Native row | M124 | FM215 |
|---|---|---|
| 127 / 1 | 1 R 59 | 1 R 109 |

This is their only row difference. Both providers have read-zero action 0 R 62;
their read-one actions differ: 59/1=1 R 72 and 109/1=1 R 42. The intended
simulation reaches the provider reading zero, so either provider works.
An exact rooted breadth-first transition-graph comparison finds no isomorphism,
even after global tape reflection. This distinction affects artifact identity
and novelty attribution, though not the size of the marker proof.

`marker-comparison.json` records the comparison, and the input files and script
are provided for an independent replay:

```sh
python3 compare_markers.py inputs/m124.native.tm inputs/fm215.native.tm \
  --out /tmp/marker-comparison.json
```

M124 native SHA-256:
`8e0ccb4b631c4e4c1c02c4b52a6fe382984e67557dd1dcd949065479e38d07b9`.
FM215 native SHA-256:
`3ece1233f11d33375425221c5bcedba941e073763912990eabf321197772dce5`.

## Scope for a later 214-state search

Zero credit enlarges the acceptable logical startup domain. A modified
initializer need not supply a theorem reserve or a theorem-valued decoded tail;
it must still reach the correct exhaustive scheduler state, theorem-valued top
and cache, and a valid physical frame. A future source pruning that preserves
completeness also need not preserve AX's numerical stack bonus. Those are
precise freedoms, not permission to omit source completeness or binary-runtime
obligations. No 214-state machine is produced by this subtask.
