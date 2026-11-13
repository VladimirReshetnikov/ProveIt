# Exact canonical syntax with one forbidden-slot mask

## Result and comparison contract

The standalone `checker_exact_mask.py` implements the same canonical closed
Eq/D public language, the same JSON integer/list certificate alphabet, and
the same acceptance relation as the existing `checker_exact.py` in
`ipra_composition_and_dummy_slots_2026-11-13`, with the usual qualification
that mathematical completeness concerns finite computations with arbitrary
finite resources. Its measurements under CPython 3.12.14 normalization are
383 significant tokens, 438 AST nodes, and 691 bytes, against 581 tokens,
641 AST nodes, and 1424 bytes for that exact-interface reference.

This is a fusion of syntax validation with the inherited opener. It does
not remove an arithmetic axiom or logical inference rule. It is not a
claim to beat the byte count of the broader 584-byte interface: that
interface admits noncanonical padding-slot spellings on which its stated
zero-padding reading is not complete.

## The syntax to be recognized

Numerical terms are variables, zero, successor, and scalar iteration
`I(n,a;u.h)`. Formulas are equations and `D_{x,y} B`. The public goal is
closed. The uniform-zero arity codec represents zero by the integer `1`
and position `j`, counted from the nearest slot, by `3+2*j`.

At a term position a unary array is successor and a ternary array is an
iterator. At a formula position a unary array is D and a binary array is
an equation. The raw codec introduces padding as follows:

| Constructor edge | Slots prepended to the availability list |
| --- | --- |
| D to its matrix | two available slots |
| Equation to either term | none |
| Successor to its child | two unavailable slots |
| Iterator to its counter or seed | one unavailable slot |
| Iterator to its update body | one available slot |

Only available slots may be named. These are exactly the transitions in
the reference's separate `term` and `formula` validators.

## The finite forbidden-slot invariant

Let the current availability list have length `p`, with position `j`
available exactly when `b_j=1`. Define

\[
 F=\sum_{j=0}^{p-1}(1-b_j)2^{j+1}.
\]

Bit zero is always zero because numerical zero is always legal. The mask
stores forbidden positions only; it does not need a high sentinel because
the inherited depth test already enforces scope. During the initial walk,

\[
 d=2p\quad\text{at a formula position},\qquad
 d=2p+3\quad\text{at a term position}.
\]

The root has `p=0,d=0,F=0`. The child depth is `d+5-r` at an array of
arity `r`, as in the original opener. This preserves the displayed depth
invariant in all five constructor cases. In particular, depth parity is
zero at a formula and one at a term.

The mask updates are

\[
\begin{array}{c|c}
\text{edge}&F'\\\hline
D&4F\\
S&4F+6\\
\text{equation}&F\\
I\text{ counter or seed}&2F+2\\
I\text{ body}&2F.
\end{array}
\]

For example, successor shifts every old slot by two, then marks the new
slots 0 and 1 forbidden; their bit positions are 1 and 2, hence the added
constant `2+4=6`. D shifts by the same amount but marks neither new slot.
The iterator shifts by one, and bit 1 is set exactly for its first two
children. The equation changes no slot.

Writing `j=0,1,2` for a child index, one table computes all the updates:

```python
(4*v + 6*(d % 2), v, 2*v + 2*(j != 2))[len(a)-1]
```

The first component handles either D or S according to the already known
sort parity. The second handles an equation. The third handles an iterator.
The arity test is performed before this table is evaluated during the root
walk, so the table is indexed only by 0, 1, or 2.

## Exact scalar test

At the closed root and all its descendants the scope floor is `k=0`.
The new scalar guard is

```python
0 <= a < d and (d & a & ~v >> a//2 & 1)
```

Python parses its second part as the bitwise conjunction of `d`, `a`,
`(~v) >> (a//2)`, and `1`. It is nonzero exactly when depth is odd, the
scalar is odd, and the tested bit of the forbidden mask is zero.

At a formula position the even depth rejects every scalar. At a term
position `d=2p+3`, the range and oddness tests restrict the scalar to

\[
a\in\{1,3,5,\ldots,2p+1\}.
\]

If `a=1`, the test examines mask bit 0, which is zero, and accepts zero.
Otherwise `a=3+2j` for a unique `0<=j<p`; the bit examined is `j+1` and
the guard succeeds exactly when position `j` is available. Unmarked high
bits cause no problem: the independent test `a<d` excludes them. Negative
references are excluded before the shift is evaluated.

The code's complete input alphabet gate is unchanged. Consequently the
objects entering the walk are actual Python integers and lists; JSON
booleans, floats, strings, dictionaries, and null cannot masquerade as
integers or lists. Nonempty invalid arities, a scalar at a formula
position, and a forbidden scalar all fail through the inherited missing
image/type mechanism. The default substitution image is the function
`c`; evaluating it as a tree raises an exception. The failure cannot turn
into a zero result merely because it is multiplied by `d%2`: Python
evaluates the recursive call before performing that multiplication.

**Exactness lemma.** The initial walk returns successfully exactly on the
canonical encodings of closed Eq/D formulas, and then returns the input
tree unchanged.

**Proof.** Simultaneously induct on the term and formula grammar. The
array arity tests select exactly the listed constructors. The mask and
depth calculations above establish the induction hypotheses at every
child. The scalar calculation establishes exactly zero or a genuine
in-scope variable. All other cases reject. On every accepted scalar the
return expression `a or 1` is just `a`, since its positive odd value is
nonzero; the returned arrays therefore equal the input arrays by the
induction hypothesis. This proves both directions and the identity claim.

## The mask is inactive during inference

The original checker uses an empty context for its initial syntax phase.
Its terminal-test expression evaluates the left operand `i(a)` before
the right-hand tuple. The latter begins by appending the neutral value
`[]` to the context. Hence the initial public-goal walk is completed while
`g=[]`, and every later opener invocation occurs with `g` nonempty.
All recursive checker calls inherit a nonempty context or an extension of
one, so no later invocation can return to the syntax phase.

The extra recursive keyword value is

```python
v = g or mask_update
```

and the scalar guard begins with `g or ...`. Once `g` is nonempty,
short-circuit evaluation bypasses both the mask arithmetic and the mask
test. The additional parameter can therefore hold the context list itself
without being interpreted as an integer. At that phase the new opener
traverses precisely the same children, in the same order, with the same
`a,t,d` arguments as the original. The use of `enumerate` merely supplies
an unused child index. All return values and all exceptions are unchanged.

This remains true for the original proof language's noncanonical internal
arrays. The mask table is never indexed there, so it adds no internal
arity restriction and does not assume that every certificate component is
a public formula.

## Why the parameter must be keyword-only

The final signature is

```python
lambda a, t=c, d=0, *, v=0: ...
```

It retains the original maximum of three positional arguments. This is
part of the correctness proof: the existing introduction uses
`i(*a,t,2)`. A unary formula supplies three positional arguments and may
introduce a binder; a binary equation supplies four and must be rejected.
Making `v` an ordinary fourth positional argument would accidentally
admit such a call and permit invalid introductions.

An initial experiment made precisely that error. Seven inherited negative
fixtures were accepted, exposing it immediately. That experiment is not
the delivered checker. The final keyword-only parameter restores every
positional arity check, and all full-checker tests pass. No input can
supply a keyword argument, since inputs are JSON data and the checker
contains no call that expands data as keyword arguments.

## Equality of the complete acceptance relations

Fix a finite JSON input. If it fails the unchanged integer/list alphabet
or is not a nonempty stack, both complete checkers reject. For a nonempty
stack with a noncanonical final goal, the reference's separate validator
rejects, and the exactness lemma makes the new root walk reject. The
timing of this rejection may differ: the new checker can consume the
first packet before discovering the invalid goal. Packet consumption on
a rejected run does not alter its acceptance value.

For a canonical final goal, the separate reference validator succeeds.
By the exactness lemma, the new root walk returns exactly the same goal
as the reference core. From the first context append onward both cores
perform the same inference operations, consume the same packets in the
same order, and have the same positional call restrictions. Induction on
their successful call trees, or direct lockstep simulation until either
rejects, proves that they have identical acceptance values.

Therefore the new standalone program accepts exactly the same finite
certificates as the exact reference. In particular it accepts precisely
the canonical closed native theorems, using the inherited canonical
soundness and completeness theorem. The established bi-interpretation
with full first-order iPRA transfers with its unchanged interpretations,
formula round trips, whole numerical domains, actual equality, and
identity numerical composites.

## Evidence

`verify_exact_fused.py` extracts the measured root lambda and the
reference's exact validator directly from their ASTs. It compares them
on 44,976 targeted, randomly generated raw, and randomly generated
canonical formulas. It also runs 50 proof fixtures against both complete
programs in normal and optimized Python, for 200 executions. The final
finite-mask checker has no mismatches in either part. Its receipt is
`checker_exact_mask_evidence.json`.

These finite checks support the implementation and exposed the positional
parameter error. The general acceptance theorem rests on the invariants
and simulation above, not on exhaustive proof search or a fresh Lean
verification. The source contains no assertions and no uncounted parser,
syntax validator, kernel, or acceptance driver.

## Optional normalization route, not used in the result

One can instead make public spellings denote a quotient in which a
reference to a padding slot is replaced by numerical zero. That approach
must actually normalize the goal before proof checking, and count the
normalizer. It cannot merely weaken the mask guard: otherwise the raw
spelling remains the goal and the second-successor-slot obstruction still
applies. The same availability information is needed to identify which
occurrences are padding, so canonicalization does not eliminate the mask.

No such root-normalizing variant is needed or claimed here. Exact
canonical validation gives a simpler proof and a direct matched
comparison with the existing 1424-byte exact interface.

## Composition with the global scope-phase profiles

The same exact syntax predicate can be fused with each independently
proved scope-phase kernel. The phase invariant must match that kernel;
one must not indiscriminately replace a separate phase variable by the
scope floor.

* In the global entry-reservation byte and AST kernels, `k` is initially
  zero. The initial `i(goal)` is evaluated before the terminal tuple
  executes `k := ~-k`, which is `k := k-1`. Every later checker invocation
  decrements it again and nothing increments it. Thus `k=0` holds exactly
  during the initial goal walk, and `k<0` throughout inference. Here `k or
  mask_update` and `k or mask_test` bypass masks in every inference call.
* In the return-reservation token kernel, a separate flag `v` is initially
  one. The initial goal walk finishes before the tuple sets `v:=0`;
  thereafter `v` stays zero. Its scope floor is decremented on returns,
  and may still be zero after validation, so the correct mask bypass is
  `not v`, not `k`. The existing arity condition `len(a)**v in (1,2+d%2)`
  is unchanged. At `v=0` even arity zero gives `0**0=1`, just as in the
  old kernel; the new mask update is bypassed and does not reject such
  internal administrative values.

With these respective invariants, the initial syntax proof is the same,
and afterward each modified kernel executes exactly the corresponding
unmodified kernel's inference operations. The certificate correspondence
between different scope-allocation protocols is inherited from the pinned
scope-phase package, not newly asserted to be identity.

### Complemented availability mask and a phase-conditional leaf test

Some AST profiles use the negative mask

\[
 F=-1-\left(1+\sum_{j=0}^{p-1}b_j2^{j+1}\right)
\]

instead of the finite nonnegative forbidden mask. Its initial value is
`-2`, and its updates are the same `4F`, `4F+6`, `F`, and
`2F+2*(j!=2)`. Python's arithmetic right shift and complement give
`~F=1+sum b_j*2^(j+1)`, which has no nonzero bits above the in-scope
positions. Thus for the initial syntax phase the range condition can be
replaced by the mask test alone:

```python
(k <= a < d if k else d & a & ~f >> a//2 & 1)
```

At `k=0`, a positive odd out-of-scope scalar tests a zero bit of `~f`,
an even scalar fails the low-bit conjunction, and a negative scalar
raises on the negative shift. Formula-position scalars also fail the
low-bit conjunction. At `k<0` the original scope test is used unchanged.
The `-2` default is essential for this variant: using finite mask zero
while omitting the independent upper-bound test would admit unmarked
out-of-scope positions.

### A uniform expression for the mask update

The transition table can also be written, on a valid root constructor of
arity `l` and child index `j`, as

```python
(f << (l+1)%3) + d%2*(6//l - j//2*2)
```

For `l=1`, the shift is two and the addition is six at a term (S), zero
at a formula (D). For `l=2`, the shift is zero and the parent is an
equation, so even `d` makes the added term zero. For `l=3`, the shift is
one, `d` is odd, and the additions for children 0, 1, and 2 are
respectively 2, 2, and 0. These are exactly the five mask transitions.
The phase bypass prevents this expression from being evaluated at
arbitrary internal proof arities, including zero.

One may cache the arity in the preceding positional argument,
`d+5-(l:=len(a))`, then use it in the keyword-mask argument. Python
evaluates arguments left to right, so `l` has been set before the mask is
computed. The assignment-expression variable belongs to the current
lambda invocation, not a recursive child's invocation. Thus this cache
preserves the original child depth and the mask update without changing
their evaluation order or adding a dependence between recursive calls.

### Expression reader boundary

If the JSON reader is replaced by the separately audited restricted
expression reader, the exactness theorem applies to its decoded
integer/list tree. This changes the accepted textual certificate syntax;
it does not give byte-for-byte identity with arbitrary JSON whitespace.
Every integer/list certificate has a supported literal spelling, so
canonical theorem completeness is unchanged. The reader and its character
gate are part of the measured standalone checker. The mask proof does
not on its own establish the reader's grammar theorem; that is a separate
composition obligation.
