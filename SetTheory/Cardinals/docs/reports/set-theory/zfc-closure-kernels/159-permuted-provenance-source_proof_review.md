# Independent review of the K216 source calibration

**Finding: no mathematical gap or blocking issue found.** This review concerns
`formalism-work/source-calibration/source_calibration.tex`, the inherited
noncommon-input command equations in the dominated-rho8 paper, the numerical
calculus definition, and the finite source constructor. It does not add another
binary runtime test or claim a proof-assistant endpoint. Input hashes and the
finite source-identity comparison are recorded in `review.json`.

## Numerical calculus and arbitrary codes

The dominated-row equivalence is stated for every natural number, rather than
only for successfully decoded formula codes. Its substitution argument uses
only arithmetic implication, truth zero, the subterm domination inequality,
and the numerical inference rules. Thus the new soundness invariant may range
over arbitrary natural top, cache, and stack codes without a hidden syntactic
filter. The permitted bundle keeps precisely its inherited inequalities on
its parameters. Generalization remains theorem-only, so no extra freshness
condition is needed.

The alias `I(0,0)=0` is handled in the place where it matters to the compiler:
`J(0)` is empty. An `MP(0)` from `(0,w,0,0)` would succeed and insert an extra
stack zero, so it could not replace that empty block. For positive `u`,
`I(0,u)>0` makes `J(u)` fail and set the counter without changing the stack.

All eight row codes are nonfalsity codes. In particular, the existential
notation in the first retained row expands through negation to an outer
implication; it does not invalidate the claim that those codes are multiples
of four. The generalized-cache code is congruent to two modulo four.

## Strong compiler and exact stack order

The stated AX output agrees with the parent command equations:

```text
[R1, R2, R3, R4, R5, R6, R7, L, Q_U(old cache), old top; old stack].
```

The quantifier body is the cache before its additive field is read, and its
binder is the counter before the other additive field is read. Therefore
`U=d`, `A=d+x`, and `B=h+y` supply the desired dominated instance with `U<=A`
for every raw tuple. The source's field order is YX.

I checked the selection suffixes using the fact that NIP tests the current
cache **before** popping the next stack head:

- `Discard` first forces MP failure with consequent `1`. Its reset AX has a
  zero gate, nine nonfalsity generated entries, and saved top zero. Exactly
  ten NIPs return `(0,w,0,0)` without inspecting the underlying stack.
- After `j` NIPs from an AX result, row `j` is in the cache. DROP makes it
  the top and pushes the old gated top. Exactly `11-j` additional NIPs remove
  that pushed top and the remaining generated entries, ending with saved
  top zero in the cache. This covers rows 1 through 8.
- The generalization construction puts `X` in the cache while the counter
  is `i`; its AX has `A=c=i`, so the gate is zero and its ninth entry is
  exactly `Q_i X`. The nine-pop selection and final three commands restore
  the original stack, counter zero, and cache zero.

For modus ponens, immediately after the two recursive blocks the retained
states evolve as follows, unless a NIP has already halted:

```text
(I(X,Y), [X;w], 0, 0)
    NIP  -> (I(X,Y), w, 0, X)
    DROP -> (X, [I(X,Y);w], 0, X)
    NIP  -> (X, w, 0, I(X,Y))
    MP(Y)-> (Y, [0;w], Y, 0).
```

This is the correct orientation: the antecedent is the top and the implication
is the cache. The reset AX has `U=A=c=Y`, hence a zero gate. Ten NIPs recover
`Y` in the cache above the inserted stack zero; DROP and two NIPs return
`(Y,w,0,0)`. If a tested cache is already `1`, the allowed early-halt outcome
of the strong contract applies. Arbitrary old top and arbitrary underlying
stack are therefore tolerated, which is essential for `Start_Y`.

## Exact packing, cofinality, and raw candidates

For both selected permutations, `Start_Y=AX(0;1,Y)` has the wire fields
`[3,Y,1]`. Its first-candidate number is consequently

```text
P(3, P(Y, P(1,R))),
```

with no outer successor. The tail `R` uses the successor convention. This
properly separates a fresh candidate from later commands, including NIP's
zero tag in the 210 permutation. Cantor pairing dominates both coordinates,
so this number is at least `Y` and supplies successful candidates above the
actual cutoff `4`.

`Start_Y` resets counter and cache for every incoming retained tuple. The
strong falsity block then either halts or returns top `1` and cache zero;
DROP, NIP, NIP tests that falsity. The proof does not need the arbitrary
incoming formulas to satisfy the soundness invariant in this completeness
direction.

Every nonhalting continuation command consumes the positive-list predecessor
before reading its fields, and each field tail is no larger than its input.
Hence continuation values strictly decrease. A fresh candidate may first
produce a tail no larger than its raw number; the finitely many continuation
steps then drain it. This covers raw numbers, missing-looking fields, and
zero aliases, without assuming that the number was intentionally packed by
the compiler.

## Finite source identity

I independently loaded the two distinct source-construction implementations:

the parent `source/build_dominated_source.py` in noncommon mode, and the new
`audit_command_permutation.py` reference constructor. On the pinned K219
source, the resulting structured trees are **exactly equal**, not merely
metric-equal. Their common metrics are 205 distinct subtrees, 4,751 primitive
occurrences, 6,176 guarded cases, maximum depth 37, and maximum zero run 8.

The changed branch bodies are closed with respect to both structured control
exits, so their normal-return contract is portable among the three selector
positions. Every small selector reaches its chosen body with the selector
register zero. The three-positive-test case leaves the correct residual
selector for AX. The exterior branch wrappers and the AX subtree stay literal. The final
checker also explicitly follows each ordinary return: the last body returns
directly to ordinal 0; the middle body returns through unconditional break
4724 to 0; and the innermost body returns through unconditional breaks 4697
and 4724 to 0. It verifies that these routes contain only unconditional
control operations and that the whole source has exactly one halting
primitive.

As a further direct source check, the next-candidate register is accessed
only at primitive ordinals 2 and 6, both in the fetch prefix. No permuted
command body changes it.

## Clarifications resolved in the final text

I reread the final source-calibration supplement. It now states the inherited
full boundary contract explicitly next to the draining argument: each
nonhalting command restores the selector and both scratch registers to zero,
preserves the next-candidate register outside fetch, and leaves the unconsumed
unpairing remainder in the proof-list register. A fresh fetch loads the current
candidate and increments the next-candidate register exactly once. This makes
the enumeration argument's full-state premise explicit alongside the four
retained-register equations. The actual represented seed has zero selector,
scratches, and proof-list register, so the stated contract applies from the
first fetch onward.

The final text also explicitly expands the negation and existential
abbreviations when justifying that all eight generated row codes are
implications and hence cannot equal falsity 1. The ordinary-return routing
checks described above are now stated alongside the closed-body argument.
All requested clarifications are resolved. The reviewed-input hashes in
`review.json` have been refreshed to the final files; this final reread did
not run any further binary runtime test.

No change to the command equations, compiler, machine table, source
permutation, or claimed consistency equivalence is required by this review.
