# Residual object/syntax proof simplifications

Snapshot: `553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`.
All paths below are relative to `Computability/DiophantineConsistency/Lean/DiophantineConsistency`.

## 1. Recover the pairing branch from its output threshold

Target: `ObjectPairingInjective.lean`, namespace `MaxSquarePairing`, theorem
`pair_eq_pair_iff`. The exact pairing is

- `b*b+a` if `a<b`;
- `a*a+a+b` otherwise.

The existing proof first shows that equal outputs have the same maximum
coordinate, using the two existing square-shell bounds. It then splits both
input comparisons independently, generating four cases. Two cases are
impossible and are disproved by bespoke cancellation/order arguments.

Add the exact lemma

```
pair a b < (max a b)*(max a b)+max a b ↔ a<b
```

It needs no discreteness premise `succ_le`; the existing nonnegative ordered
semiring assumptions suffice. In the first branch the inequality reduces to
`a<b`. In the second, the output is the threshold plus the nonnegative `b`,
so the strict inequality is false.

If `he : pair a b = pair c d` and `hm : max a b = max c d`, rewriting this
lemma gives `a<b ↔ c<d`. The injectivity proof now splits only `a<b`; each
branch determines the comparison of `c,d`. This deletes the two mixed cases.
The shell-bound proof and `succ_le` remain essential to establish `hm`.

This differs from prior canonical pairing-witness proposals: those select
auxiliary witnesses from known inputs; this theorem derives the branch from
a common output and shell and simplifies injectivity over an arbitrary
ordered semiring. It neither assumes an external `Nat.sqrt` operation on a
nonstandard omega nor changes the pairing definition.

Static accounting: the old declaration has 33 nonblank lines. The replacement
plus the new helper has 28 nonblank lines. The whole file falls from 104 to
100 physical lines. The body-only reduction is larger, but must not be
reported as the net improvement. The new branch invariant is the chief gain.

`ShellPairingBefore.lean` contains the exact extracted generic baseline with
only imports and namespace changed. `ShellPairing.lean` is the modified
generic segment. The full project candidate and patch retain the namespace,
public `pair_eq_pair_iff` signature, and all object-level application code.

## 2. Use the constructor equation before transporting list-head order

Target: `ObjectListHead.listHead_le`.

The old positive-code branch converts `left_le_pair` into an existential
additive slack using `le_iff_exists_add`, converts the target back to a slack
existence goal, constructs `code≠0`, unfolds `listHead`, substitutes the code
constructor, and finishes with associativity/commutativity.

The already existing `ObjectNumericWire.head_cons` theorem says exactly that
`listHead (cons a b)=a+1`. Once `zero_or_cons` supplies the constructor case,
the complete positive branch is

```
  · rw [hc,ObjectNumericWire.head_cons]
    exact add_le_add (left_le_pair H _ _) (le_refl 1)
```

The zero branch is unchanged. No helper is introduced. The entire original
13-nonblank-line declaration becomes 5 lines; the whole file loses 8 lines.
This is a small concrete residual improvement after the ordered-semiring
interface already exists, not a proposal to introduce that interface again.

`ListHeadMonotone.lean` checks the consumer proof abstractly with precisely the
existing zero/constructor/head/bound hypotheses. The full candidate uses the
actual upstream declarations, but must still be compiled in the production
import graph. Its mathematical applicability does not rely on ordinary Nat
induction or a standardness assumption.

## 3. Build the internal linear order from its strict-order facts

Target: the `LinearOrder` instance in `ObjectNaturalOrder.Natural`.

The current instance proves reflexivity, transitivity, antisymmetry,
totality, and the compatibility of `<` and `≤` manually. Its actual
mathematical inputs are only `nat_no_self`, `nat_transitive`, and `nat_linear`.

Construct `IsStrictTotalOrder` for the relation `mem x.val y.val`, then use
mathlib's `linearOrderOfSTO`. The strict-total-order proof has three fields;
all routine nonstrict-order laws come from the library. The entire subtype
continues to contain all model-internal naturals, including nonstandard ones.

There is an important concrete representation issue. `linearOrderOfSTO`
defines `x≤y` as `x=y ∨ mem x.val y.val`, while the old instance reduces it to
`mem x.val y.val ∨ x.val=y.val`. These are logically equivalent, not
intentionally definitionally equal. The replacement includes

```
theorem le_iff_LeRel (x y : Natural H) :
    x≤y ↔ LeRel H x.val y.val := by
  change (x=y ∨ mem x.val y.val) ↔ mem x.val y.val ∨ x.val=y.val
  simp only [Subtype.ext_iff,or_comm]
```

Five local boundary conversions are included in the candidate: the two
directions of `le_iff_exists_add`, `zero_le`, and the two additive-order
fields. The original model-level `LeRel` definition stays unchanged. Strict
membership remains definitionally equal to `<`; two prototype examples
record the exact new relation projections.

The source inventory found no explicit `LeRel` consumer outside
`ObjectNaturalOrder` in the object modules, but that is not an elaboration
proof. Rebuild the downstream object-order, division, pairing, and list-head
clients before adoption. The prototype is a checked general constructor once
its log succeeds, not a claim of full integration validation.

The instance alone drops from 35 nonblank lines to a 15-line block including
the compatibility lemma. After charging the five boundary conversions and
changed import, the whole file falls from 175 to 160 physical lines. This
controlled definitional change is appropriate only if the integration build
confirms that its interface cost remains this small. A trial that preserved
the old `≤` by definitional equality consumed the savings rebuilding the
minimum/maximum/comparison data, and was discarded.

## Novelty review and scope

The prior-audit agent read a-f research reports and all 12 incoming archives.
Its targeted searches found no strict-total-order construction and no
output-threshold pairing branch recovery. The direct list-head transport is
not explicitly present; its nearest antecedent is broad advice to exploit
the already existing internal ordered-semiring interface. It should be
presented as a small new application, not as a new algebra framework.

Discarded directions: generic internal formula-code catamorphisms,
constructor views plus unique-existence induction, internal recursive-graph
preservation/fusion, generic definable induction transport, arbitrary-model
to sealed-derivation bridges, scanner fusion/guarded folds, and PR congruence.
Those are already covered and are not recommendations in this packet.

## Validation scope

Use `checks.json` and the corresponding `.log` files as the authoritative
statuses of the final prototypes. A zero exit code with no `sorryAx` validates
only the stated prototype or extracted segment. `source-metrics.json` records
original source hashes and static measurements. The three full candidate
modules and patches are integration proposals, not compiled module results.
No equation, witness count, executable primitive-recursive program, or
consistency theorem is changed or strengthened.
