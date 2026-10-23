# Size metadata for the closed direct quartic

The direct endpoint in `DirectQuarticZFC.lean` has executable coefficient syntax,
degree at most four, and an unconditional external Lean theorem that its lack
of natural solutions is equivalent to `ConZFC`. It compiles
`NativeZFC.representation` directly to a quartic, before the Jones compression
used by the nine-variable endpoint. This note concerns the size of that actual
closed recipe.

An exact evaluation of the compacted variable count has not completed. The
metadata modules instead prove a conservative finite upper bound without
constructing the enormous expression tree. The final statement is
`DirectQuarticSize.variableCount_lt`: the number of natural variables is less
than `2^300000`. This bounds the binary length of the count by 300000 bits;
it is neither the exact count nor a lower bound.

## Checked recurrences

Let `m` be a representation's witness count and `h` its integer-expression
depth, with leaves at depth zero. `RepresentationSize.lean` proves that
splitting into two natural expressions gives total tree size `S` satisfying

- constants and variables: `S = 2`;
- addition or subtraction: `S = 2 + S_left + S_right`;
- multiplication: `S = 6 + 2*S_left + 2*S_right`;
- always: `S + 2 ≤ 2^(2*h+2)`.

The unsimplified quartic has exactly `m + S + 1` variables. Simplification and
removal of unused source witnesses cannot increase this count. Thus input
metadata suffice to bound the final compacted count.

`GraphSizeBounds.lean` proves that the invariant

```
expressionDepth ≤ 6*witnessCount + C
```

is preserved by nonempty graph substitution and by graph addition and
multiplication. The native fixed formula and stack blocks admit `C = 512`.
Their bounds are obtained by arithmetic folds on their shared constructor
descriptions; evaluating their expanded expression trees is unnecessary.

The bounded-universal template has an especially simple exact count. If its
input residual has `m` witnesses and total split size `S`, its output has

```
m*(4*S + 11790) + 10*S + 20674
```

witnesses. Its depth is at most

```
2*m + max 16384 (12*h + 1) + 96.
```

These are theorems of `BoundedForallDepth.lean`. The fixed primitive graph
witness counts used in the recurrence are 111 for exponentiation, 598 for
binomial coefficients, and 1697 for factorial. The proof never treats these
primitives as supplied semantic assumptions. Their representation correctness
comes from the existing checked Pell and arithmetic constructors.

## Applying the recurrences to the actual source

`NativeEnumerationSize.lean`, `NativeEnumeratorBounds.lean`, and
`IterationSize.lean` certify the following metadata:

| Source object | Witness count | Expression-depth bound |
|---|---:|---:|
| native enumerator step | 1742 | 10964 |
| optional-state step | 1752 | derived from the invariant |
| transition equality before the single bounded quantifier | 1782 | 11204 |
| transition family after the bounded quantifier | exact recurrence above | 138109 |
| closed refutation representation | bounded-family count plus 39 | 140000 |

The transition equality uses the existing natural-relation equality graph,
including its two internal graph witnesses. `IterationSize.iterate_depth` and
`iterate_witnessCount` identify the named rows with the existing actual
iterator; no replacement computation or unproved compiler equivalence is
assumed.

`DirectQuarticSize.lean` bounds the closed representation's witness count plus
one by `2^22426`. Together with depth at most 140000 and monotonicity under
simplification/compaction, this yields the advertised `2^300000` bound for the
actual direct quartic. No decimal expansion of these large bounds is required.

## Verification and limits

The Lean checks are `checks/RepresentationSize.lean`,
`checks/NativeEnumerationSize.lean`, `checks/IterationSize.lean`,
`checks/BoundedForallDepth.lean`, and `checks/DirectQuarticSize.lean`.
They audit theorem dependencies as well as the relevant closed metadata. The
proofs use only Lean's usual `propext`, `Classical.choice`, and `Quot.sound`
axioms, sometimes a subset. No native-evaluation axiom, admitted lemma, or
existential choice of polynomial coefficients is introduced.

The bounds do not establish a size advantage over the nine-variable equation.
They expose the cost of the current tree-based graph and quartic compilers.
A constructor layer that preserves shared arithmetic registers is a separate
next target, supported by the generic shared-DAG quartic compilers. It must
supply its own checked connection to the actual proof-certificate checker or
enumerator before a smaller closed equation can be claimed.

The internal object-ZFC theorem proving the unsolvability/consistency
biconditional remains a separate obligation. The external Lean equivalence
and the numerical metadata do not discharge that obligation over nonstandard
models of ZFC.
