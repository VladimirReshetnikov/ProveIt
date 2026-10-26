# HA proof relation: author checkpoint

The new packet defines actual intuitionistic first-order arithmetic proof existence. Both new sources were read completely and compiled freshly, sequentially, with Lean v4.32.0, `-M6000 -j1`, and `Elab.async false`. Both builds returned 0. No accepted source, shared object, equation, or graph was changed.

## Exact scope

`DiophantineConsistency.HA.Derives` uses the existing `SetTheory.PA.Term` and `Formula` types. Its 16 constructors are precisely assumption, implication introduction/elimination, falsity elimination, conjunction introduction/projections, disjunction introductions/elimination, universal introduction/elimination, existential introduction/elimination, equality reflexivity, and Leibniz equality elimination. It has no unrestricted excluded-middle or double-negation-elimination constructor and no semantic reflection or choice rule.

The complete context is shifted at universal introduction; existential elimination shifts both the old context and its target. Both instantiation rules use the existing capture-avoiding term substitution. `Relative B G a` permits a finite list of axioms from `B`. `Proves a` takes `B = PA.Formula.Ax_s` and an empty context. The reused axiom predicate is exactly universal closure of successor injectivity, successor nonzero, addition zero/successor, multiplication zero/successor, and every first-order formula induction instance. This uses neither the shallow `PA.Model.induction` field nor induction over all Lean predicates. Thus `Proves` is conventional HA theoremhood over the same syntax as the existing classical PA calculus.

`Derives.erase` and `to_classical` only forget the intuitionistic restriction. Their direction is HA to classical PA. Neither supplies a classical-to-HA translation, target consistency equivalence, arithmetical current-equation formula, nor serialization of a proof. The user's target is existence of an HA proof; the `Prop`-valued inductive proof relation and finite existential axiom list support exactly that target.

## Checks

The checks establish all six arithmetic axioms, arbitrary first-order induction, a concrete universal eigenvariable shift, `forall x exists y, x=y`, the full existential-elimination shift signature, concrete Leibniz equality symmetry, ex falso, and empty-axiom identity. The only comparison check is the one-way classical erasure. The ten axiom reports contain only `propext` and `Quot.sound`; `Derives.erase`, `to_classical`, the quantified reflexive witness and the existential-elimination signature depend on no axioms. This is a metatheoretic dependency audit, not a claim that imported classical modules have become intuitionistic derivations.

## Authenticated prerequisite reuse

The complete five-module custom import closure is `PAHF.PASyntax`, `PAHF.AckermannHFCore`, `FirstOrder.Completeness`, `FirstOrder.Calculus`, and `FirstOrder.Fol`. Every current source byte was compared to `/home/codex/src/Proofs`; all hashes match, as do `lean-toolchain` and `lake-manifest.json`. Corresponding prior compiled objects were referenced only in a new private overlay. This is source-identical compiled-object reuse, not a fresh rebuild of the 66,936-line PASyntax monolith or its prerequisites. Relevant complete syntax, calculus-constructor, binder and axiom-definition ranges were manually read; no claim of a full manual read of that monolith is made. The mathlib packages are reused with the matching package manifest/toolchain.

Private overlay: `/tmp/ha-proofs-deps-3joi8dkg`. Full sources, objects, commands, logs, read scope and rechecked pins are recorded in `ha-proofs-dependency-replay.json`. No prerequisite object was overwritten.

## Frozen files

- `HAProofs.lean` (147 lines): `c4af3acb35ed46bd4d1dc36eba36500ff0254e69c6e552aa3cef9b468a1cd943`; fresh object `66103e7b07e3992fee919880c79d04f2d11bf2a7312b02a35530f3704300ddcc`.
- `HAProofsChecks.lean` (65 lines): `0e7aa30344f16944029a4fe0933b2cf8c18e316e5579659f2048788fb4321c1a`; fresh object `c739ed0577b6c65731daf5f380f9d0c4cf4b8a4053b36fdd3617126bab5c568e`.
- Dependency receipt: `f8163c4c5325f30e1e9adfa04fbe3501ef67518072c46ed411b94531ea7ee4ba`.

Author: circuit_reduction. This is an author receipt; independent review remains separate.
