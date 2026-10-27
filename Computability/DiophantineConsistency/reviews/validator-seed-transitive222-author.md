# Actual raw and tagged transitive source certificates — author checkpoint

Author: `circuit_reduction`. Status: the final fresh main/check pair passed;
independent ROOT review and replay remain separate. I authored this pair and
several of its seed-source prerequisites, so this is not an independent review.
No accepted proof source, dependency, shared object, or umbrella was changed.
No Git command was run.

## Exact result and mathematical scope

The only main import is `ZFCinPA.ValidatorSeedLogicalImages222`. In each
**Type0** model of `IΣ₁`, the new module constructs actual proofs in the concrete
`ValidatorFullSeedTheory222.Source V` and certifies their codes with the actual
`Proof seedTheory` predicate:

* `raw_transitive a` proves an existential container containing `a` whose every
  member is a raw subset of that same container.
* `tagged_transitive a t` proves, under the source formulas `emptyAt t` and
  `t ∈ a`, a container `c` with `t ∈ c`, `a ∈ c`, and closure under tagged
  predecessors of tagged members. There is no supplied transitive container,
  `U ≠ t` condition, freshness hypothesis, or standardness restriction.
* `tagged_pair x y t` proves, under `emptyAt t`, a tagged container whose tagged
  members are exactly the source-equality alternatives `z = x ∨ z = y`.
  This stronger guarded-test form does not require `x` or `y` themselves to be
  tagged. Coincident coordinates and marker collisions are retained.

The raw proof fixes the actual binary seed matrix `singleton(input, output)`.
It first obtains a singleton of `a`, then one full-seed container. Its request
part puts `a` in that container. For `y ∈ c` and `z ∈ y`, a singleton of `z` is
a subset of `y`; the **full closure of the same seed witness** supplies an
output in `c`, and singleton uniqueness identifies that output with `z`.
The implementation uses the accepted public `full_member_closure` contract.
It does not replace that closure by the weaker support-only image.

Both tagged constructions use accepted guarded comprehension with the literal
truth matrix. The cut therefore preserves precisely the tagged members of the
constructed raw bound. All free-parameter shifts, existential openings and
generalization contexts are explicit. Longer implication chains use genuine
finite-context deduction and modus ponens; there is no model-validity oracle.

`rawTransitiveProof_isProof`, `taggedTransitiveProof_isProof`, and
`taggedPairProof_isProof` certify the selected source derivation codes.
The total raw formula constructors have concrete `Σ₁` graphs and exact
typed/raw bindings. Their arguments are term codes, not labels. The `.get`
proof selectors are **not** asserted to have `Σ₁` graphs.

This packet does not prove profile conversion, coded Eqv/Member laws,
QHyp/quotient/WF calibration, a CP/container schema, ZF/ZFC proof calibration,
or the desired HA equation equivalence.

## Final source and artifact pins

Sources are under `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/`.

| File | Lines | SHA256 |
| --- | ---: | --- |
| `ValidatorSeedTransitive222.lean` | 793 | `53e600acb96561fb29cc1771a47ca0e2e5f99124a709bb7cfe5d7b5b5e52aec7` |
| `ValidatorSeedTransitive222Checks.lean` | 77 | `79c4fd7f0afdb6c8058c5cd465ec60ed8efcd4386d5f93deb849d410ca0a2e26` |
| Main fresh object | — | `dd04c8a90ba6ef19b7a67b39c23b0b25926a3db34b308bc60dacee041b4baf9a` |
| Checks fresh object | — | `9a4ea196a17c39c96a305ce240dc7f7a35fda25784ae6367b5aa7135ccb0a37e` |

Final private output root:
`/tmp/validator-seed-transitive222-author-wimnj8oq/attempts/1793111456567832523/lib`.

Final replay summary `validator-seed-transitive222-replay.json` SHA256
`8d29e8dac0889757e8cdc89bef659907192aa0b45cf7251c3e13e5f88e899bb6`;
cache inventory `validator-seed-transitive222-cache.json` SHA256
`4c3f10084e15adb6c81c55653e0e710ed162e93086b5cc542cf17e9867c18d5d`;
63-file author replay manifest SHA256
`94f2eae8b3c632c70ae0e3345955bd0717673676594d9d9aa52dcf31a93fe502`.

## Reuse, fresh execution and checks

ROOT authorized the exact **217 cached modules /136 Foundation modules /
625 cached artifacts /45 explicit external boundaries /670 actual first
artifact providers** closure, with zero prerequisite refresh. The selected
LogicalImages provider is the accepted ROOT
`/tmp/validator-seed-logical-images222-root-sx91r5e8/lib`.
The historical cache qualifications remain in the unchanged pinned plan and
input records. This is a fresh two-leaf result, not a fresh whole-closure build.

The preparation reauthenticated the approved source headers and reachable DAG,
compiler/toolchain/package pins, inherited records, and every selected first
provider. Each attempt rechecked **13,466** inherited/explicit pin observations
before and after execution. Final freeze performed **14,365** observations,
including the actual search-path first providers, final source snapshots,
logs, timings, objects, and exact unchanged dependency headers.

Both final compiler commands used the pinned Lean 4.32.0 binary with
`-M6000 -j1 -DElab.async=false`, `LEAN_NUM_THREADS=1`, an explicit private
`LEAN_PATH`, fresh regular nonsymlink output files, and a checked 512MiB disk
reserve before each command. Commands and search paths are recorded verbatim.
Main: exit 0, **81.056 seconds**, empty log. Checks: exit 0, **3.538 seconds**,
no warnings. All **17** reports use only `propext`, `Classical.choice`, and
`Quot.sound`. These are Lean metatheory audits, not new source-theory axioms.
Peak reported RSS was 2,009,216 KiB for main and 1,925,168 KiB for Checks.

Focused checks cover the three source judgments, actual derivation-code
certificates, singleton matrix orientation, expanded raw-transitivity binders,
free/shift identities, typed/raw constructor agreement, sparse internal
labels, repeated coordinates and marker collisions. The complete final
793/77 sources and all executed preparation/build/freeze code were read;
all intermediate proof deltas were read before their next bounded attempt.

## Preserved development and proposal correction

All five attempts retain both input snapshots before their first compiler
command, driver, exact commands, status, logs, timings, and any produced
objects. Attempts 1–3 failed on elaboration: opaque-helper unfolding, nested
binder normalization, context-preserving simplification, finite proof-search
resource handling, quote/vector/numeral bindings, and notation parentheses.
They took 125.805, 118.305 and 82.728 seconds respectively. Attempt 4 main
passed cleanly in 80.517 seconds; its checks emitted all 17 standard reports
but failed two literal expansion controls at `rfl`. Attempt 5 changed only
those controls to explicit unfolding/simplification and passed both leaves.
No public theorem premise, import, resource cap or cache scope was changed.

The frozen original proposal incorrectly named the downstream profile-pair
interface in section 3. The preserved separate addendum
`research/validator-seed-transitive-plan-addendum.md`, SHA256
`3e6dc41e74022bde600f6639185ad217ef7aa54404be3a80ce0824b09cf0ac76`,
records the source-bound correction identified by `complemented47_review`:
`ProfilePairs.Pair` uses **ClassMember/Same**, not the later interpreted
Member/coded Eqv. `KLowerEqv.tag_pairs` converts exact raw pairs to that
profile predicate directly. The original proposal and its manifest remain
unchanged; this pair makes no such profile-conversion claim.

The durable bundle also preserves the original planning evidence and ROOT
authorization, all attempt records, and the complete executed drivers.
Immutable input metadata and terminal records are regular hardlinks to save
space; all paths and bytes remain present. Compiled output objects were
independently produced and remain at their separately pinned attempt paths.
Per-attempt authentication records refer to one immutable pinned inventory
instead of duplicating its large path lists.
