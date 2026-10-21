# Source-only comparison of the 58-step generic core

The exact upstream core is a useful next checkpoint: it removes the auxiliary seed interface and proves lifting and composition inside the same condensed-detachment derivation. The mathematical source read and a separate free-constructor check are clean. This packet does not claim a Lean compilation, producer reproduction, or endpoint recheck.

The reviewed upstream source is Git `d93adc41745b28830efd865d2b9898be36988ef5`, `DominatedImplication.lean`, SHA `e91f5cf8e6583ba73221362bc21438b70897a8808329886dc615c166bb16edd7`. It is also byte-identical to the core in root's later `2ca3a5c16f0876d2cab842056353c03a1ed2f5f0` nine-path manifest at `/tmp/k215-phase10-upstream-review/inputs.json`. The checked phase10 comparison source is SHA `5e524b3fd128e91ae1be067ec12392978713b29c129a37b55272cc4091c9bf3f`.

| Artifact | Checked phase10 | Proposed upstream | Difference |
|---|---:|---:|---:|
| Generic core bytes | 14,739 | 13,984 | −755 |
| Generic core lines | 330 | 295 | −35 |
| Generic core + unchanged Nat adapter bytes | 17,419 | 16,664 | −755 |
| Generic core + unchanged Nat adapter lines | 403 | 368 | −35 |

The core alone is 5.12% smaller; these are source-file measurements, not proof-term, compilation-time or whole-repository savings. The Nat adapter remains 2,680 bytes/73 lines, SHA `8fdbec0db9134070bee2dfa0a433aff66ab83c00007ea7b9aabd9192c506d378`.

## Mathematical change

`Language`, the executable definition `rho8`, and `Restricted` are byte-identical. The three public theorem statements `rho8_all`, `composition`, and `lift_right` are identical after expanding the same explicit `h : Restricted L T` section binder. There are no new imports or semantic assumptions: only reflexivity and insertion into either implication operand justify the relation guards. No truth value, numerical code, decoder, injectivity, transitivity, or normalization equation enters the proof.

The old generic port carried a private `WithSeed` interface, proved the 52 steps with a temporary theorem `T τ`, then discharged that interface with a restricted reflexive row. The new proof supplies that already-available row locally at its five uses (`d4`, `d9`, `d13`, `d18`, `d22`):

```
T (rho8 L a a a a), from h.rho8 a a a a (L.refl a).
```

Its complete syntactic formula is used as the discharged antecedent. Nothing identifies `a → a` with `a`; in particular, this is valid for arbitrary constructors as well as the native zero alias. The four earlier filler choices in `d3`, `d7`, `d10`, and `d16` remain reflexive choices of the restricted row's actual first parameter.

All 52 old numbered conclusions recur in the 58-step list (some are renumbered; the mapping in `source-audit.json` compares conclusions rather than asserting guard-text identity). Six additional conclusions provide a shorter compatibility route. The useful mathematical boundaries are:

- `d53`: `((a → (b → c)) → d) → ((a → c) → d)`.
- `d55`: `(a → b) → ((x → a) → (x → b))`, internalized lifting.
- `d58`: `(a → b) → ((b → c) → (a → c))`, composition.

The other new steps are `d32`, `d51`, and `d57`; their explicit applications and guards were checked as well. `rho8_all` is the unguarded `d56` instance; `composition` is `d58`; `lift_right` is one final MP using `d55`. Thus the five local seed replacements and six extra schemata eliminate the old seed structure/discharge and the separate compatibility tail without weakening the public endpoint.

## Checks and limits

The own, read-only `read_source.py` parses the Lean statements and proof applications as free constructor terms. It checked every one of the 58 private MP applications, every one of the 23 restricted-row invocations, their reflexivity/insertion/hypothesis guard proofs, and exact statement conclusions. Earlier theorem references must already be registered. The three short public bodies were also read directly. There are 59 MP uses including the final public lifting application, and no seed uses. The parser is a diagnostic independent of Lean; its PASS is not kernel acceptance.

The source contains no `WithSeed`, `h.truth`, numerical-zero normalization, `sorry`, or native evaluation shortcut. All six public declarations and the unchanged adapter boundary were compared. We read the upstream renderer's core emission/goal selection and its header/tail definitions only to identify the production boundary; this is not a complete producer or search-program review. No supplied Python/Rust program was imported or executed, and no compiler or canonical mutation occurred.

The root nine-path Git manifest is authoritative for the proposed merge. Five raw research files can remain attributed upstream data while the checked core and maintained producer stay fixed. In particular, upstream `generate_dominated_implication_lean.py` merely relabels the old phase-eight producer as historical. Replacing the current phase10 producer with it would lose the current deterministic production path.

## Concrete next step

Use the exact 58-step core as the next isolated Lean/API/axiom candidate, retaining the exact Nat adapter. If that passes, update the current self-contained maintained producer to read pinned inert proof/derivation data and validate explicit applications, rather than importing the supplied renderer. Preserve its CLI and reproduction controls. Then refresh the affected descendant closure with transitive source invalidation and unchanged endpoint clients. There is no need to rerun source/site coverage merely to assess this static proposal; any actual reuse decision belongs to the reviewed integration driver.

No machine/state reduction, new Rocq result, PA theorem, faster kernel, or accepted phase11 endpoint follows from this review. The checked phase10 source remains the current boundary until a separately recorded kernel and integration run succeeds.

Authorship: the reviewer authored the prior phase10 generic adaptation and maintained producer. This is a fresh source comparison and diagnostic of the new upstream proposal, not an independent peer of the reviewer's prior proof.
