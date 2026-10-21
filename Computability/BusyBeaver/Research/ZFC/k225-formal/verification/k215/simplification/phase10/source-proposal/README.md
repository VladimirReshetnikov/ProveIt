# Generic 52-step dominated implication draft

This is an API-preserving adaptation of the submitted 52-step proof at
`4fdc59197a45a6beb7e5a4ae7109fd13477b1d17`. It changes the private proof in
`DominatedImplication`, retaining its representation-independent assumptions
and the exact current `DomRho8` adapter. No machine, source program, calculus
row, or endpoint statement changes.

The final core is `candidate/DominatedImplication.lean`, SHA-256
`5e524b3fd128e91ae1be067ec12392978713b29c129a37b55272cc4091c9bf3f`.
It is 14,739 bytes / 330 lines, compared with 19,378 bytes / 381 lines for the
maintained baseline. With the unchanged 2,680-byte / 73-line adapter, the pair
falls from 22,058 to 17,419 bytes: **4,639 bytes and 51 lines removed**.
These are proof-source measurements, not a claim of net repository savings.

The source-only author audit checks all 58 explicit private proof bodies:
52 submitted steps and six compatibility helpers, containing 66 modus-ponens
applications, 19 restricted-row applications, and five seed detachments.
It compares constructor trees literally and does not normalize implications.
The public `Language`, `rho8`, `Restricted`, `rho8_all`, `composition`, and
`lift_right` interfaces are unchanged; the adapter is byte-identical.
Kernel execution and producer reproduction are separate, parent-owned steps.
No compiler or supplied generator was run by this author.

## Removing numerical assumptions

The four uses of `0 ≤ A` are choices of a discarded fourth-input filler.
Each paired major/minor occurrence is replaced by that restricted row's exact
`A`, so its guard becomes reflexivity:

| Lemma | Replacement for both local zeros |
|---|---|
| d3 | `imp v1 v2` |
| d7 | `imp (imp v1 v2) v3` |
| d10 | `imp v1 v2` |
| d16 | `v0` |

In d4, d9, d13, d18, and d22, the truth-detachment argument becomes the private
seed `τ`. The major premise is literally `τ → conclusion`. There is no use of
`imp τ τ = τ`, a least element, injectivity, or transitivity of the insertion
relation. The unchanged `withSeed` discharges `T τ` by taking
`τ = rho8 L a a a a`, whose restricted guard is reflexive.

## Retaining composition and lifting

The submitted numerical file omits the current composition/lifting APIs. The
generic successor restores them without the old helper hierarchy:

* `under_antecedent` combines d47 and d46 in two detachments. It sends a proved
  `x → y` to a proved `(z → x) → (z → y)`.
* `insert_middle` inserts one antecedent into d16. Together with Peirce d18,
  application d35, unrestricted d52, and contraction d22, it proves the
  explicit application-contraction and application-transport lemmas.
* `repeated_antecedent` removes a repeated antecedent after two arguments.
  Applying it to the transported application row gives the exact current
  composition schema `(a → b) → ((b → c) → (a → c))`.

These named helpers are retained as mathematical boundaries, rather than
inlined solely because some have one caller. Every application and relation
guard is explicit; no deduction or arbitrary-code substitution rule is added.

## Maintained producer successor

`production/generate_dominated_implication_lean.py` is a self-contained draft
with the current `--out LEAN_ROOT` / `--check` CLI. It reads the exact attributed
Lean rendering and derivation as pinned **data**, applies the nine adaptations,
and validates all 58 bodies with the same free-constructor reader. The final
output hash and three template hashes are exact gates. The adapter template
is unchanged. The original raw Lean input already exists in the published
phase-nine source-review history; the submitted renderer/search is neither
imported nor executed. The historical submitted CLI remains untouched.

The producer has passed an inert Python AST parse only. Root owns actual
generation controls and kernel checks. The earlier import-based producer was
rejected before execution and is preserved under `history/producer-import-draft/`.
The first author source-reader attempt misparsed a binder containing `: T`;
its original source and diagnostic are retained in `history/`. The corrected
reader selects the final conclusion. This was a metadata-parser failure, not
a Lean rejection. The earlier pending-status comment and its first source
audit are retained in `history/draft1/`; the final proof tokens are unchanged.
