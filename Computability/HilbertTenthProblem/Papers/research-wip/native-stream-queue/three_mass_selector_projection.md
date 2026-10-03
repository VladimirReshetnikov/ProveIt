# Removing one selector per step from the three-mass certificate

A guarded projection removes one natural selector witness from every nonempty
source step. The full native increment/decrement example drops from **56 to
47 operations** and eight to six witnesses. The corresponding compact cleaned
clock drops **56→46**. A three-increment chain drops **107→91** native and
**105→88** compact-clean, with eighteen to fifteen witnesses. Degree rises from
two to three. These are fully paid fixed-horizon circuits, not a new universal
polynomial bound.

The parent is the [mass-coordinate compiler](three_mass_arithmetic.md), source
SHA256 `d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0`.
Its authenticated original native and cleaned producers come from the two
immutable archives at `4e270aa4648c5fd7e18626507531046715976535`. The new
[compiler](three_mass_selector_projection.py) uses their full exported
certificates, not selected rows or a simplified known execution.

## A nonnegative gate for the missing selector

At each step choose a fixed branch k to be implicit. Keep natural selectors
`e_j` for `j≠k` and every natural branch mass `v_j`. Put

\[
 S=\sum_{j\ne k}e_j,\qquad e_k=1-S.
\]

Substitute this expression into every original affine square and endpoint.
The one-hot square becomes identically zero and is omitted. Replace the old
inactive-branch sum by

\[
 G=S(S-1)+\sum_{j\ne k}(1-e_j)^2v_j+S v_k.
\]

For every natural supplied tuple, `S(S−1)≥0`, each squared-factor product is
nonnegative, and `S v_k≥0`. Thus `G≥0` on the entire natural orthant, including
assignments where the restored `e_k` would be negative.

If `G=0`, integrality gives `S∈{0,1}`. When `S=0`, all explicit selectors are
zero, the restored selector is one, and the squared-factor gates force all
explicit-branch masses to zero. When `S=1`, exactly one explicit selector is
one, the rest are zero, `e_k=0`, and every inactive mass, including `v_k`, is
zero. Conversely any natural one-hot selector tuple with its inactive masses
zero has `G=0` after omitting `e_k`.

The new complete polynomial is the sum of all remaining affine squares and
these G terms. Its natural zeros therefore restore exactly the parent's
one-hot and inactive-branch conditions, and every remaining row is literally
the parent row under the restoration. This proves a **bijection of complete
natural zero fibers**: projection forgets `e_k`, and restoration sets it to
`1−S`. The parent mass-coordinate theorem then restores natural offsets
`u=v−e`. Input, state sequence, final value and physical time are preserved.
Uniqueness of the original natural fibers transfers as well.

This proof does not assume a valid source execution in order to establish
positivity. It first proves all selectors and inactive masses valid from the
nonnegative polynomial terms; the retained source equations then apply.
The implicit branch is fixed at compilation, not chosen by an uncharged
run-time decision.

For `B≥1`, the core witness count becomes `(2B−1)h`, from `2Bh`. At `B=1`, the
only selector is restored to one and G is identically zero. At `B=0`, there is
no selector to project; the original `(-1)^2` one-hot rows remain at positive
horizon, so an empty source acquires no new accepting execution. At `h=0`,
nothing is projected and all original halt and endpoint conditions remain.
The proof is uniform in the allowed source table and external horizon.

## Exact polynomial relation and an unsafe alternative

After restoration the old selector total is exactly one. Its old inactive sum
is `sum_(j≠k) (1−e_j)v_j + S v_k`. Consequently, on every integer or rational
tuple, not just at zeros,

\[
 F_{\rm new}(z)=F_{\rm mass}(\iota(z))+
 \sum_t\left[S_t(S_t-1)+\sum_{j\ne k_t}e_{tj}(e_{tj}-1)v_{tj}\right].
\]

Here `iota` restores only the omitted selectors; the parent mass coordinates
and external endpoints otherwise stay fixed. This is a formal coefficient
identity with an explicit correction, **not equality of the two polynomials**.
The natural zero-set proof uses integrality. No general nonnegative-real or
signed-integer zero-set equivalence is claimed.

Simply substituting `e_k=1−S` and dropping the old one-hot row is unsound. In
the actual `INC2;DEC2` source at horizon one, omit branch 1's selector and use

```
x=4, e_0_0=2, v_0_0=5, v_0_1=0, y=10, T=1508.
```

Every supplied coordinate is natural, but the restored selector is `−1`.
The naively substituted **complete** parent polynomial is zero: the two
control squares contribute 1 and 4, and the inactive sum contributes −5.
The source needs two steps to halt. The guarded new polynomial instead equals
12 on this same tuple. The published receipt evaluates both complete circuits;
this is not an isolated gate counterexample.

## Paid schedules and degree

The emitter compiles every affine form after substitution, including `N0=x+1`,
all state and value rows, the native or compact-clean clock, and any endpoint.
It uses the parent's grouping of equal coefficients, exact common-expression
reuse, constant/zero/one folding and final dead-gate removal. Every surviving
binary addition, subtraction and multiplication is counted, including
nonunit fixed coefficients, all squares and all final sums. No value computed
by the baseline emitter is reused as a free input to the new circuit.

Three literal G schedules are available: the displayed direct form; factoring
`S(S−1)+S v_k` into `S(S−1+v_k)`; and, for two branches, the Horner form

\[
 G=(1-e)\bigl((1-e)v-e\bigr)+e v_k.
\]

The latter is the same polynomial as
`e(e−1)+(1−e)^2v+e v_k`; it costs six operations before sharing with the rest
of the complete circuit. For other branch counts the Horner mode uses the
direct schedule. Such duplicate emitted forms are not distinct optimization
results.

The bounded census tries every single implicit branch used uniformly at all
steps, and all three schedules, across 38 actual native/compact-clean
certificates. It does not exhaust arbitrary per-step choices or arbitrary
arithmetic circuits. The implementation also accepts an explicitly supplied
per-step choice list, covered by the same mathematical construction; that
larger search is not part of the numerical minimum claims below.

| Actual source and endpoints | Parent best mass schedule | New M | New A | New total | Core witnesses | Implicit branch |
|---|---:|---:|---:|---:|---:|---:|
| `INC2;DEC2`, h=2, native y,T |56|18|29|47|8→6|0, Horner|
| `INC2;DEC2`, h=2, cleaned T |56|19|27|46|8→6|0, Horner|
| Three `INC2`, h=3, native y,T |107|28|63|91|18→15|1, factored|
| Three `INC2`, h=3, cleaned T |105|28|60|88|18→15|1, factored|
| Prime-three zero test, h=1, native y,T |30|9|15|24|4→3|0, Horner|
| Already halted empty source, h=0, cleaned T |5|2|3|5|0→0|none|

The baseline is the minimum of the two actually emitted parent mass schedules;
the earlier construction records its separate old-offset comparisons. No
claim of an optimal baseline circuit or optimal new source is made.

Whenever `B≥2` and `h≥1`, the complete degree is exactly three: some retained
selector/mass pair contributes `e_j^2 v_j` with coefficient +1, and no other
term cancels it. The substituted affine squares have degree at most two.
When no such branch pair exists, the displayed endpoint-bearing cases remain
exactly quadratic. Thus the witness and operation savings have an explicit
degree tradeoff. A degree-two endpoint-penalty construction is a separate
alternative, not something silently composed into these counts.

## Scope and checks

This is a research emitter for freshly generated authenticated certificates,
using the same explicit fixed-name interface as its parent: free raw input x,
native free output/time y,T, or compact-clean free time T. It is not a hostile
packet validator or a general hygienic replacement for the original compiler.
The branch table and source horizon are external parameters. The raw value's
valuation interpretation is not a supplied ordinary-counter decoder, and no
fixed-arity unbounded-history representation is inferred.

The deterministic receipt contains 252 complete coefficient identities with
the displayed correction, 1,008 signed full-output identities, 816 complete
natural projection/restoration fixtures, and all six worked sources above.
It also enumerates 5,655 local natural gate tuples and verifies their exact
zero condition; a separate complete-certificate census covers 5,060 natural
core tuples with actual affine endpoints and finds nine zeros, all restoring
natural original offsets and a zero original polynomial. The false one-step
halt above is explicitly rejected. These finite tests supplement the uniform
nonnegativity and zero-fiber proof.

Replay from any directory, with the parent in the WIP root:

```sh
python3 three_mass_selector_projection.py \
  --root /path/to/native-stream-queue --repo /path/to/Proofs \
  --expect three_mass_selector_projection.json
```

`--output PATH` writes a fresh deterministic receipt. The helper authenticates
the parent before execution; the parent then authenticates the immutable
archives and executed producer bytes. It changes no original report, archive,
producer or Git state.

The [independent complete-source review](review_three_mass_selector_projection.md)
reads the full construction and reconstructs all252 coefficient identities,
1,680 affine rows,516 step penalties and18,847 paid live gates from the actual
exporter certificates. It separately checks24 mixed-index/clock variants,
9,534 local natural tuples and3,066 complete natural tuples, including every
zero's original natural lift. Root read the independent helper and note and
freshly replayed both author and independent receipts. No change was requested.
