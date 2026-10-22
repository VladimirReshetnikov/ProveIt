# Direct Infinity from the seed property

Snapshot: `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.

## The mathematical simplification

The maintained Lean proof obtains ordinary Infinity by first constructing a
container closed under tagged singletons, passing to the bisimulation quotient,
constructing a singleton index, constructing finite attempts, proving agreement
and existence for those attempts, and taking a Replacement image.

The seed property already provides the closure needed for ordinary successors.
Its closure clause allows an input `x'` whenever `x'` is a subset of the current
container member `y`. Choosing `x' = y` uses only reflexivity of subset.
This observation gives a constructive, general theorem:

> If `SeedProp mem R a` holds, `P a`, every `R`-output satisfies `P`, and
> `R` is serial on `P`, then some raw set `C` contains an `R`-successor of
> `a`, every member of `C` satisfies `P`, and every member of `C` has an
> `R`-successor in `C`.

There is no choice of an infinite sequence and no recursion theorem in this
argument. Each needed successor is selected inside an existential proof.

For the K215 lower calibration take an empty raw marker `t`,
`P(x) := t in x`, and

```
Succ(x,y) := forall z, z in y <-> z in x or z = x
R(x,y)    := t in x and Succ(x,y).
```

The existing `raw_aug` theorem, at the true matrix, gives `Succ(x,y)`.
If `t in x`, then `t in y`, so the marker is preserved automatically. This is
why ordinary successors work directly here, while raw singleton formation
does not preserve membership of the marker.

The tagged set `e = {t}` is empty in the tagged domain: any raw member equals
`t`, and `t` itself is untagged because membership is irreflexive. Apply the
general theorem at `e` and adjoin `e` to its output container using the existing
bounded tagged comprehension theorem. The bound is a transitive container of
the raw pair `{C,e}`. This gives an ordinary inductive set in the actual tagged
domain.

Finally, an exact raw successor descends to an ordinary successor of the
bisimulation quotient. If interpreted membership is

```
Member(z,y) := exists u, rawMem(u,y) and Eqv(z,u),
```

then

```
RawSucc(x,y) ->
  (Member(z,y) <-> Member(z,x) or Eqv(z,x)).
```

After taking the quotient, `Eqv(z,x)` is literal equality. The empty witness
and inductive container descend explicitly, yielding exactly the current
`ZFAxioms.inf` conclusion.

## Equality and definability are checked explicitly

`KLowerSeed.FormSeed` quantifies every `Form`, with no equality-free restriction.
It occurs downstream of the equality/indiscernibility bridge. Thus the use of
literal equality in the successor formula is justified at this interface.
The proposal makes no claim that this matrix is directly available at the earlier
equality-free seed interface.

With output in slot 0 and input in slot 1, the exact successor matrix is

```lean
fAll (fIff (fMem 0 1) (fOr (fMem 0 2) (fEq 0 2)))
```

The marker is the first parameter, hence slot 2 outside that binder:

```lean
fAnd (fMem 2 1) successorF
```

`KLowerDirectInfinity.lean` proves their satisfaction equations and instantiates
the actual maintained `FormSeed`, `raw_aug`, `raw_pair`, `raw_transitive`,
`tag_of_bound`, and `Tag` definitions. It imports `KLowerTag`, avoiding the
later `tag_singleton_closed` construction and the final ZF module.

`KLowerDirectInfinityQuotient.lean` uses the actual `KQ1Model` quotient and its
`mk_eq_iff`. Its output is the exact existential/empty/successor formula of
the present semantic Infinity axiom. It accepts the existing `QHyp` interface;
the proof body does not use its singleton field. Both actual adapter modules
passed the recorded Lean check, along with their full 40-module source closure.

## Integration proposal

1. Extract a `KQ1ZFCore` from `KQ1ZF` that accepts an explicit ordinary Infinity
   proof. Keep the existing base, replacement, power, well-founded closure and
   model-construction arguments.
2. Preserve `KQ1ZF` as a compatibility facade. It supplies Infinity by the old
   singleton/finite-attempt route and calls the common core.
3. In `KLowerQHyp`, supply Infinity using `ordinary_quotient_infinity` and the
   already established `tag_qhyp`. Its exported `zf_consistent_of_formSeed`
   theorem can retain its current statement and name.
4. Rebuild all affected descendants, the exact K215 endpoint, and compatibility
   clients. Check that no new axiom appears in the existing endpoint reports.

The proposed import change can remove `InductiveAttempts` from the K215 proof
closure. The original file has 397 physical lines and 18,624 bytes in this
snapshot. This is a candidate dependency removal, **not a demonstrated net
source reduction**: the new modules and the shared core must be counted, and
the final endpoint has not been rebuilt with this replacement.

`FiniteSets` and `SingletonInfinity` still occur through `WellFoundedPart`.
They must not be counted as removed. The old singleton argument also remains
necessary to fill the current nine-field `QHyp`, even though this Infinity
proof does not use that field. A later split into an eight-field quotient core
and a separate Infinity provider could remove that now-superfluous premise
from the K215 path. That additional API refactor is separate from this result.

## Verification scope

`DirectInfinity.lean` supplies five checked core theorems: general serial closure,
the tagged container, the actual subtype restriction, quotient successor, and
quotient Infinity. The first three reports are axiom-free; the last two report
only `propext`.

`SeedSerial.v` is the constructive Rocq/Coq counterpart of the general serial
closure theorem. It compiled with Coq 8.18.0 and passed recursive `coqchk`; its
assumption report is closed. This does not certify the Rocq 9.1 production
endpoint or substitute for a repository-specific Rocq adapter.

The actual Lean adapters passed after correcting explicit section-binder
inclusion, documentation placement, and a subtype equality rewrite. Failed
logs are retained separately. Its `tagged_infinity` report uses only the
repository's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.
The quotient adapter additionally needed the correct `ProfileCollection.Eqv`
namespace; the successful `ordinary_quotient_infinity` report has those same
three standard axioms. There is no admitted lemma in either successful module.
The reproduction driver builds the complete selected adapter closure afresh,
serially, from sources; its manifest binds every source hash and compiler exit.

This is a new mathematical route and a checked local implementation. It is
not an updated proof receipt for `KEndpoint215`, not an internal PA proof,
and not a ZFC-encoded derivation of the final equivalence.
