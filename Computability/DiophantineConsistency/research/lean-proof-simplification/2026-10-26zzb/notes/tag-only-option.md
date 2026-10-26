# A nine-line cleanup after the existing certificate-dependency proposal

This packet contains a **small incremental simplification**, measured against the already-proposed semantic split in:

`docs/incoming/ProveIt_Proof_Simplification_Review_2026-10-26.zip`

at closing repository snapshot `3b51c69d42ff99bc420698532af3fe1d1f9bd356`.

The baseline member is:

`ProveIt_Proof_Simplification_Review/reference/certificate-migration/EnumeratorSemantics.lean`.

Apply the earlier archive's `patches/01-certificate-dependency.patch` first, as required by the user's instruction to assume prior proposals applied. The new patch in this packet is measured against that resulting 85-line semantic module, not against the original `Computability.lean`. The dependency reversal itself is existing work and is not a contribution of this packet.

## New change

Remove three unused private declarations from the extracted semantic module:

- `stateEquiv`, the equivalence between the six-register state and a nested tuple;
- the `Primcodable St` instance transported along that equivalence;
- the `DecidableEq St` instance obtained from the encoding.

Replace the now-obsolete `Mathlib.Computability.Primrec.Basic` import with `Mathlib.Logic.Encodable.Basic`. The semantic definitions still need natural-number notation, function iteration, sets, and the encoding of Boolean results; the narrower import supplies those dependencies. Removing all Mathlib imports would be incorrect.

The exact change is **85 to 76 physical lines**, with no replacement helper in the production module: **nine lines and three declarations removed**. All executable definitions and semantic theorem bodies remain textually unchanged. Do not combine this measurement with the earlier report's removal of its separate 32-theorem primitive-recursiveness chain.

## Why this is valid

A failed computation is observed by testing whether an `Option St` is `none`. Deciding that proposition needs only the outer constructor. Lean supplies

```lean
Option.decidableEqNone (o : Option α) : Decidable (o = none)
```

for every type `α`, with no `DecidableEq α` or `Encodable α` assumption. The elementary identity

```lean
@decide (o = none) (Option.decidableEqNone o) = o.isNone
```

is proved by cases on `o` followed by reflexivity. In particular, the six register values do not need an encoding to decide whether the enclosing option is `none`.

The earlier incoming report explicitly retains the state-equivalence/instance scaffold conservatively (report line 131). This packet discharges the specific concern that removing it could change decision data. The comparison file re-elaborates the original incoming semantic source with its original scaffold, imports the separately compiled cleaned module, and proves:

```lean
theorem baseline_eq_cleaned :
    PriorSemanticLayer.haltingTest =
      DiophantineConsistency.haltingTest := rfl
```

This is definitional equality of the literal natural-valued function, not merely an equivalence between accepted inputs. It also tests the possible effect of replacing the Mathlib import on typeclass selection.

## Files

- `patches/tag-only-option.patch`: the only new production delta; applies after the earlier certificate-dependency patch.
- `proposed/DiophantineConsistency/EnumeratorSemantics.lean`: the complete resulting 76-line semantic module.
- `lean/TagOnlyDecision.lean`: exact predecessor-source comparison and the `rfl` theorem above; the predecessor's namespace is changed solely to permit comparison in one environment.
- `lean/TagOnlyTargetAudit.lean`: imports the cleaned actual module, verifies its literal decision expression and zero-step evaluation, and prints axioms of the actual exported declarations.
- `EnumeratorSemantics.log`, `TagOnlyDecision.log`, `TargetAudit.log`: successful compilation/audit logs.
- `provenance.json`, `validation.json`, `semantic_dependency_sources.json`: exact baseline, target, compiler, source hashes, and scope.

The patch was checked with `git apply --check` against the exact predecessor. Temporary build files are not included.

## Verification

The cleaned production module compiled successfully with Lean 4.32.0 and Mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`. Its 14 repository semantic dependencies, totaling 4,091 source lines, were independently checked against pinned `7ba7d102822df1eff376cbca913727d9d588ab4e` Git blob identities and freshly compiled; the root review established that this closure is unchanged at the closing snapshot. No stale `Computability` object file was used.

Both comparison and target audit compiled successfully. The patch applies cleanly to the exact incoming 85-line baseline. The actual declarations `haltingTest`, `haltingTest_eq_one_iff`, and `exists_haltingTest_eq_one_iff` report only `[propext, Classical.choice, Quot.sound]`; there is no `sorryAx` or new axiom. The generic constructor-observation theorem is axiom-free. No reduction in the existing axiom set is claimed.

This is a targeted semantic-module verification, not a whole-repository build or a new verification of the already-proposed dependency reversal. No timing improvement is claimed.

## Novelty boundary

The exclusion audit found no occurrence of `decidableEqNone`, the tag-only decision argument, or removal of these three retained scaffold declarations in the 43 archived packets and seven current incoming archives. The immediate predecessor deliberately retains them. The eligible residual is their deletion and the proof that the existing executable observation is unchanged. The much larger supplied-code-to-computability refactor is excluded prior work.
