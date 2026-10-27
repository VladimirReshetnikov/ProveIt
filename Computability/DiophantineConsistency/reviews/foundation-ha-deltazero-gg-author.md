# Bounded ordinary/GG comparison inside HA: author receipt

26 October 2026. Author: `circuit_reduction`. This is the approved second
leaf of [the frozen bounded-formula proposal](../research/ha-foundation-deltazero-bridge-audit.md).
The preceding `FoundationHADeltaZero` main and checks remain byte-identical.

The 194-line `FoundationHADeltaZeroGG.lean` proves, for the actual Foundation
predicate `DeltaZero p` and arbitrary bound/free term environments `bv,fv`,

```text
HA.Proves
  ((ordinaryAux bv fv p → formulaAux bv fv pᴺ) ∧
   (formulaAux bv fv pᴺ → ordinaryAux bv fv p)).
```

These are literal PAHF object-language conjunction and implications.
`pᴺ` is Foundation's existing `Semiformula.doubleNegation`; no syntax type
or negative-translation algorithm was defined. The proof is an induction on
the actual arithmetic hierarchy derivation, with explicit level zero.
Positive-level unbounded/alternating constructors are excluded numerically.
`ordinary_gg_equivalence_relative` retains the result under any finite open
context by genuine HA weakening.

Positive atoms use the previously proved HA equality/order decisions to
eliminate exactly their double negations; negative atoms already have the
same literal interpretation. Conjunction transports both implications.
`encoded_or_equivalence` uses genuine decisions of the two ordinary
components to recover their disjunction from the literal negative encoding.
There is no generic disjunction DNE rule.

Bounded universality preserves Foundation's actual NNF guard disjunction:
its negative order atom is identical in the ordinary and GG interpretations,
and the existing HA order decision decides that negated atom. The proof
normalizes this disjunction and recloses using the accepted capture-safe
`all_imp`. It does not silently treat the source guard as a primitive
intuitionistic implication or identify the bound with its witness.

For bounded existence, the conjunction of the ordinary order atom and matrix
is compared with the literal GG conjunction. The forward negative existential
encoding is intuitionistic without any decision premise. The reverse helper
`encoded_ex_equivalence` explicitly requires
`HA.Proves (dec (.ex a))` for the **whole ordinary existential**, not merely
decisions of its instances. The actual bounded case supplies this premise
from the accepted `hierarchy_zero_decidable (.bexs ht hp) hs bv fv`, retaining
the source's positive-bound condition. `not_ex_all_not` shifts all assumptions
under its eigenvariable and uses the exact PAHF instantiation/rename identity.
No positive unbounded-existential DNE or Markov principle occurs.

The 66-line checks pin the literal existing GG interpretations of positive
equality, negative order, disjunction and existence by `rfl`; exercise actual
nested bounded-all/bounded-ex with a bound referring to the preceding
witness; retain negative equality and positive order atoms, sparse free
parameters, nontrivial term environments and shifted finite contexts; and
explicitly retain the whole-existential decision premise in the recovery
helper. Nine axiom reports use only standard Lean axioms. The five public
finite logical helpers report only `propext` and `Quot.sound`. The hierarchy
and endpoint inherit `Classical.choice` through the preceding positive-bound
extraction proof; this is a metatheoretic dependency, not a new HA rule.

I fully read the source GG definition and rewrites, actual HA contextual
quantifier constructors and derived rules, both new source files, and the
complete private replay driver before running it. The final cache was
independently traversed from current source imports: 102 cached modules,
76 Foundation modules, 330 cached artifacts and 34 explicit external
package/toolchain boundaries. No cached client imports either new leaf.
Both original DeltaZero author evidence and the accepted root primary are
authenticated, including the complete original 44-file attempt bundle.
The selected root record has SHA
`a5c29762b19d1d1ec273ee2fa5b948dbd9d4c695e29bf123119b8803be78cf59`,
and the primary actually imported is
`/tmp/foundation-ha-deltazero-root-peer-_0nkrho9/lib/DiophantineConsistency/FoundationHADeltaZero.olean`,
SHA `8077e247871af1b704e106824370382c23f2f8d1f9a5f410758a2fe8c675a567`.
All 692 distinct final pins are checked before and after execution.
There was no Foundation or prerequisite compilation.

Only these two new leaves were compiled with Lean 4.32.0,
`-M6000 -j1 -DElab.async=false`, regular new private outputs, and the 512MiB
reserve. Final main/check PASS took 2.571s/1.800s. Main log is empty;
checks contain nine standard-only reports. Private primary:
`/tmp/foundation-ha-deltazero-gg-author-6hg8_ur8/lib`.
The first main attempt failed because a multiline `exact` continuation was
indented as a new command; adjusting that indentation fixed it without
changing any definition or theorem statement. Its full snapshot, diagnostics,
command and input pins are retained. No failed checks or prerequisite builds
occurred and no resource limit was raised.

Frozen pins:

- Main source: `7e9b0d0c0a71f7cceeb9ed3751ea36e95aa007224543ee7dbdb4f88e3ce1486b`.
- Checks source: `1518f6be2a5a1d9623d472a3b8d854e1b75074e02bd255d04874fbcb11666b67`.
- Main object: `f9f8d84acd4726cfacc6f2c7eb1bad8d1f1666fbb54230421ebb09a774042a3a`.
- Checks object: `e3e540cb281e1c544fd28e2c1e27a63c04eabc6f88026b89980217509f157640`.
- [Replay summary](foundation-ha-deltazero-gg-replay.json): `3f52779825d4938ce48af364d165a72aad48ba3e0f634ec65f64acf2475a1563`.
- [19-file manifest](foundation-ha-deltazero-gg-replay/FILES.json): `89fbdfca8ce394e171513c6c1f96e697b94cd2cbf858df4beb0a99269f0920fb`.

This comparison requires an actual syntactic DeltaZero derivation. It does
not identify Foundation's delta-one proof checker with a bounded formula,
normalize the actual consistency checker, supply unrestricted Σ1 stability,
or prove the maintained equation's HA consistency equivalence. No frozen
source, vendor file, shared document, equation artifact or Git state changed.
