# Internal full-seed source constructor and finite basis: author receipt

27 October 2026. **Author fresh pair PASS; independent acceptance pending.**
Author: circuit_reduction. Final main 426 lines; Checks 82 lines. Both complete
sources, every development change, and the preparation, build and freezing
drivers were read before their relevant execution. No accepted source,
shared object, equation artifact, shared documentation or Git state was changed.

## Exact result

The module uses precisely the accepted `ValidatorFullSeedTheory222.seedTheory`:
source equality, literal membership irreflexivity, and the universally closed
instances of the unchanged full seed body. In every arithmetic structure with
the explicit IΣ1 model instance, it constructs, for **every internally typed
two-slot matrix** `K`, the following:

```lean
seedInstanceCode K.val = fullSeedBodyVal K.val
SeedR (closedSeedCode K.val)
closedSeedCode K.val ∈ seedTheory.Δ₁Class
Proof seedTheory (openSeedProofCode K.val) (fullSeedBody K).val
openSeedProof K : seedTheory.internalize V ⊢! fullSeedBody K
(openSeedProof K).val = openSeedProofCode K.val
```

The three constructors have explicit fixed Σ1 graphs, proved correct on all
raw inputs. Only their typed-body identity and proof claims require typing.
The proof code is the existing represented closing/specialization constructor,
not a code selected from a supplied standard proof or a completeness theorem.
No standardness, closed-matrix or bounded-free-label premise is imposed.

The recognizer parameter is the literal internal negation of `K`. Its bounded
parameter condition follows the actual identity-substituted negative matrix
occurrence in the full body and typed NNF negation involution. Thus the
accepted negative parameterization recognizes the exact positive full body.
`closeFormulaCode_schemaRecognizer` handles all its free parameters and internal
closure length. `openAxiomProofCode_isProof` then reopens this recognized axiom
using actual internally represented specialization. The result is not merely
standard quotation membership.

The same source theory also has actual internal source proofs of:

```text
∃ c, ∀ y, ¬(y ∈ c)
∃ c, ∀ y, (y ∈ c ↔ y = t)             for every internal source term t
∃ c, t ∈ c                            for every internal source term t
∀ t, ∃ c, t ∈ c
∃ t, ((∀ y, ¬(y ∈ t)) ∧ ∃ c, t ∈ c).
```

These are `Source V ⊢ ...` derivability conclusions, not model-level set
existence assumptions. Checks also convert the empty and arbitrary-singleton
conclusions to the actual raw `Provable seedTheory` predicate. All statements
retain the IΣ1 model structure explicitly; none is asserted as a new HA
derivation.

## Finite source derivation

`pairMatrix` is literally the accepted full body with its outer `∀ A ∃ C`
removed. It retains all five substitutions and the nested closure component.
`pair_exists` specializes the newly constructed full-body proof. From the
actual conjunction, `pair_support` and `pair_request` derive the needed
existential projections through genuine source proof rules.

For the false matrix, support makes every candidate member impossible, giving
the empty object. For the matrix `y = t`, request plus source reflexivity gives
a member equal to `t`; actual membership congruence gives `t ∈ c`. Support
gives the converse restriction on all members. Source symmetry and membership
congruence yield the full singleton biconditional. The singleton therefore
makes the tag domain inhabited for every marker. Existential monotonicity
combines this with an empty marker, with both witnesses under their actual
object-language binders.

Source reflexivity, symmetry and membership congruence are obtained from their
literal quoted equality axioms in `seedTheory`. Their NNF shapes, including
the terminal truth/falsum and the four-binder order of relation congruence,
are bound explicitly. No interpreted `Eind` is identified with primitive
numeric equality; these are proofs in the source language itself.

The source language is function-free. `term_is_fvar` uses its actual internal
term classification to show that an arbitrary zero-bound-slot term is an
arbitrary internal free label. This is not a restriction to standard labels.
It permits exact substitution calculations while preserving all parameters.
All existential elimination and universal introduction steps expose their
actual `.free`, `.shift`, shifted finite contexts and lifted vectors. Local
irreducibility attributes only prevent the elaborator from expanding private
encoded-syntax wrappers; the corresponding literal identities are proved.

## Focused checks and limits

Checks cover all three total graphs, arbitrary typed code, actual recognizer
and theory membership, the explicit proof code, true/false matrices, a nested
matrix with sparse free parameters 17 and 31, repeated shifts of arbitrary
matrices and terms, every basis endpoint, raw source-provability conversion,
and exact singleton/tag/empty binder slots. The seventeen axiom reports use
only `propext`, `Classical.choice` and `Quot.sound`.

The finite basis does not assert raw CP/GIC, arbitrary comprehension, a
shift-fixed free-marker predicate, tagged Collection, bisimulation, quotient
well-foundedness or an interpretation of ZF/ZFC. The marker-reserving
represented interpreter and the genuine QHyp/quotient route identified in
the approved plan remain open. This packet supplies their authorized source
constructor and nonempty basis prerequisites. It proves no new decimal215
runtime bridge, polynomial witness calibration or closed HA equivalence.

## Authenticated reuse and execution

The exact imports are `ZFCinPA.ValidatorFullSeedTheory222` and
`ZFCinPA.ModelCodedOpenSchemaAxioms`. The private provider is
`/tmp/validator-seed-source-basis222-author-hd5e4nyg/lib`.
The frozen cache has 200 current-source modules, including 136 Foundation
modules, 608 artifacts, and 45 explicit boundaries including Init and meta
Aesop. The approved accepted FullSeedTheory provider and historical source-
bound open-specialization providers are retained with their original
trace/companion qualifications. This is authenticated dependency reuse,
not a fresh whole-closure replay. No prerequisite was compiled or refreshed.

Preparation snapshot: `b4f140c632be8dcb5da307816b8a9b9e68fb586e`.
Every selected source header was checked, including `public meta import`.
The freeze independently recomputes the exact reachable dependency DAG and
checks all 245 custom/external first object providers against the actual
search path, with Init resolved through the pinned compiler's library.
No reused client imports either new leaf. Cached files are symlink inputs;
the only compiler outputs are the two new private regular files.

Each build rehashes the selected sources, objects, explicit boundaries,
compiler, toolchain, manifest and parent receipts before and after execution.
The final run records 2,582 observations, and freezing also rehashes all 952
inherited route-plan observations. The durable `closure-reauth.json` records
the current headers and first providers. The original route markdown/JSON,
initial import inventory, executed planner and preceding v1 are preserved
unchanged in the author bundle.

Only the new pair was freshly compiled with Lean 4.32,
`-M6000 -j1 -DElab.async=false`, `LEAN_NUM_THREADS=1`, no `LEAN_SRC_PATH`,
and the 512 MiB reserve guard. Final timings were 32.373/3.508 seconds.
The main log is empty; Checks contain exactly seventeen standard-only reports
and no warnings. The unchanged clean main object matches its preceding pass.

All twelve attempts are retained: nine failed main compilations, a passing
pair with provisional Checks and linter notices, a clean main followed by
failed expanded Checks, and the final clean pair. Failures concerned local
names/typeclass inference, literal equality-axiom NNF shape, typed vector and
context rewrites, closed-code elaboration timeouts, and quantifier parentheses.
The two final Checks failures were implicit syntax inference in the existing
raw-provability adapter, resolved by supplying its exact sentence parameter.
No cap was increased; no failed object is used as acceptance evidence.

## Frozen pins

- Main: `89cb03dae589494db007f42b030d9234613c4e02f35d91307a1bfcd3acdd8c03`.
- Checks: `504062d9c42cc974827c9fc6f0b9f1390c9d122931ef4e796e93b5b6dd5dfb5a`.
- Main object: `b386be3407776eded2b468241fd7bdd41528fe87345bbae6f360c7f37bf8df22`.
- Checks object: `696c70906d11d9ac3d33983aeb70f59a0f31f779e62e09e640fad9f522156477`.
- [Cache inventory](validator-seed-source-basis222-cache.json): `50b2bf50c57fe2632e4b28b1028aa537dc00bdbca129666ebc65e6b6cfc40946`.
- [Replay summary](validator-seed-source-basis222-replay.json): `c19fcc42ee10f3c48c1d0cc6fed1fb2838ad08538820466516a6c6b37a0c78fa`.
- [117-file manifest](validator-seed-source-basis222-author-replay/FILES.json): `9bbeadf8153e6033bb9d1aae5a0e4def79c08c7c9a12742e057e7a9d0f264f55`.
- [Approved route plan](../research/validator-seed-tagged-interpretation-plan.md): `6bd9bc2a292d1892b5bd07db6f5acb9822872629175bca40240424420a11b35b`.
