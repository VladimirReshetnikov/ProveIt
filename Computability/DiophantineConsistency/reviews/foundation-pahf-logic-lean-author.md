# Foundation intuitionistic Hilbert proofs to HA derivations

Author: `circuit_reduction`. This is an author review and fresh leaf execution,
not an independent peer review. The complete Foundation `HilbertProofᵢ`
constructors and finite-context definition, target `HAProofs` and `HADeduction`,
relevant PAHF binder identities, both new files and both cache/freeze drivers
were read before execution. Both final new sources were reread before freeze.

## Frozen files

| File | Lines | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/FoundationPAHFLogic.lean` | 167 | `431b93234df5cbdba8d61f18f1b648c30f7993760df36679a3badf4bdb0d2868` |
| `Lean/DiophantineConsistency/FoundationPAHFLogicChecks.lean` | 72 | `6ae887cbfe776b8ccc7e7f543d6e7cb49731e12d76f679b137c0cb7bdcb00e76` |
| `reviews/foundation-pahf-logic-dependency-replay.json` | — | `59795d945342dadaafc99e2bd9e81c977cbdbbe40a1bbd4f70630ac4abaaf01a` |

The final selected-source/object recheck at repository snapshot
`b806592e04eb2005f67881846a1c3717ddb15076` found no selected dependency drift.
The frozen syntax packet remains unchanged.

## Exact proved interface

`ofHilbertProof` recursively maps every actual Foundation `HilbertProofᵢ`
constructor to `HA.Derives []` in PAHF syntax. For an arbitrary supplied Hilbert
system it explicitly requires a proof of each translated extra axiom. This
conditional helper does not assert any arithmetic-axiom transfer.

`intuitionistic_proof` discharges that hypothesis for the actual Foundation
`𝗜𝗻𝘁¹` system, whose additional axioms are precisely EFQ instances:

```text
HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ ℒₒᵣ) φ
  → HA.Derives [] (FoundationPAHFSyntax.formula φ).
```

Every propositional schema is constructed using target natural-deduction
introduction/elimination rules. Generalization uses the frozen exact
one-variable `formula_free` identity and `HA.Derives.allI` with empty shifted
context. Universal distribution and existential elimination are proved with
the actual target shifted contexts; the fresh-variable specialization uses
PAHF's proved `subst_instTerm_var_zero_rename_up_succ` identity. Existential
introduction and universal specialization use the actual singleton source
substitution vector, explicitly identified with a constant `Fin 1` environment.
No eigenvariable condition is silently dropped.

`finite_proof` maps an actual Foundation finite-context proof into
`HA.Derives (Γ.map formula) (formula φ)`. Foundation defines that source proof
as a Hilbert proof of `⋀Γ → φ`; the new proof builds the translated conjunction
from the very same list of target assumptions. The empty and singleton cases
use the source's actual `conj₂` convention. Duplicates and list order are
retained. No source assumption is discharged as an arithmetic axiom.

`finite_provable` accepts genuine intuitionistic proof existence and returns
the same target derivability proposition. Its elimination of the source
`Nonempty` proof occurs into `Prop`; no choice or serialized proof is required.
The focused checks exercise EFQ, all four quantifier schemata/generalization,
two assumptions, duplicate assumptions, empty-context logic and proof existence.

## Fresh execution and cache scope

Direct sequential main/check commands, source/object/log hashes and all added
prerequisite pins are recorded in the JSON receipt. The private overlay is
`/tmp/foundation-pahf-logic-5wtwdiqt`. Both commands used Lean 4.32.0,
`-M6000 -j1`, and source-level `Elab.async false`.

Both terminal exit codes are zero. The main's final log is empty; all 14
checks' axiom reports contain exactly `propext` and `Quot.sound`. No final
warning, `Classical.choice`, `sorry`, custom axiom, `native_decide`, semantic
reflection, or classical-to-HA oracle occurs in these endpoints.

Fresh main object:
`282caadcd5dc343681911691321e9678c429713384a0f2f8caf2e30ce7e3fc82`.
Fresh checks object:
`28fda49abacbcf9fbce7ed77ebca7077b25703697ab47cf9f39c652caff269f5`.

The exact 64 custom prerequisites from the syntax manifest were reused after
source/object/trace checks. Three additional frozen leaves were reused under
source/object pins: `FoundationPAHFSyntax`, `HAProofs`, and `HADeduction`.
No prerequisite was freshly rebuilt in this packet. This is not a fresh replay
of Foundation, PAHF, Mathlib, or the current equation closure. No shared object,
accepted source, vendor file, umbrella or Git state was changed. Early local
elaboration failures involving dotted constructor inference and singleton
substitution notation were fixed before the final successful builds; they do
not affect the frozen theorem signatures.

## What remains open

This packet proves a logical proof map into the genuine `HA.Derives` relation.
It does not prove conventional HA arithmetic/order/equality axioms translated
from Foundation's Peano theory, induction-schema transport, the comparison of
sentence-closure conventions, or a target `HA.Proves` theorem for a Foundation
arithmetic derivation. Foundation's existing GG result is still used upstream;
its recursion is not duplicated here. The current equation and exact215-machine
internal arithmetic calibration and final HA consistency-equivalence theorem
remain separate obligations.
