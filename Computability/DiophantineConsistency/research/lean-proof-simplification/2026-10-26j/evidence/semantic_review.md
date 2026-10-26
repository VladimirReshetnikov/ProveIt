# Semantic simplification findings

Snapshot: `8e8b5dcb954969621c484588f0b902be1cfea7b3` of
VladimirReshetnikov/ProveIt. All production paths below are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

The novelty agent read the two loose incoming ZIPs and the earlier placed
simplification report linked by `docs/incoming/README.md`. The following
topics were explicitly excluded: generic validated history folds, `Produces`
and fragment assembly, encoded scanner simulation, primitive-recursive
iteration laws, list lookup replacements, Boolean tag reflection, witness
layout naturality, semiring specialization, and `omega_ind_of_spec` transport.
The ideas below are narrower, materially different additions. They are not
claims of global mathematical originality.

## 1. Prove the exact decoder graph once

### Source evidence

`AnnotatedProofCode.lean:78-105` proves `Tree.decoded_depth_le` in 28
physical lines. Lines 107-132 prove `Tree.quote_of_decode` in 26 lines.
Both induct on fuel, split zero/nonzero codes, inspect the first unpair
coordinate, and split the same two recursive `Option` results. The first
proof retains the rank information; the second retains the code information.

The repeated branch tree can prove their conjunction:

```lean
theorem decode_sound {fuel code : Nat} {t : Tree}
    (h : decode fuel code = some t) :
    t.quote = code ∧ t.depth ≤ fuel
```

Keep both existing public theorem names as one-line projections. Then expose
the exact graph characterization:

```lean
decode fuel code = some t ↔ t.quote = code ∧ t.depth ≤ fuel
```

The reverse implication follows from the existing `decode_quote`, after
rewriting the supplied code equality. This characterization also supplies
fuel monotonicity of successful decoding and rejection below the necessary
depth. It is sharper than a mere sufficient-fuel bound.

### Concrete artifact and result

`semantic_prototypes/DecoderFusion.proposed.patch` replaces a 56-line region
(including separating blank lines) with 38 lines: 18 fewer physical lines.
It preserves `decoded_depth_le` and `quote_of_decode` and does not modify the
decoder, quotation, parser, or later theorem statements. `git apply --check`
succeeded against the pinned source. **The production patch was not compiled**:
the project Mathlib build products are unavailable in this environment.

`semantic_prototypes/DecoderGraph.lean` is a checked core-only analogue. It
uses an abstract binary code with explicit one-step inspection laws, defines
the fuel decoder, and proves the fused theorem and exact graph iff. It was
compiled by Lean 4.32.0. The successful log records only standard Lean axioms
(`propext`, `Quot.sound`, and, for the iff theorem, `Classical.choice`), with
no `sorryAx`.

An additional, closer validation is `semantic_prototypes/ExactDecoderFusion.lean`.
It transplants the production `Tree`, quotation offsets, depth, decoder, and
the exact combined proof from the proposed patch. Only `Nat.pair`, `Nat.unpair`,
and `Nat.pair_unpair` are replaced by explicit parameters. This tests the
production arithmetic and Option proof branches with the matching compiler.
Its final successful log has only the standard Lean axioms `propext` and
`Quot.sound`. It still does not check the production imports or downstream
dependency graph.

### Why this does not repeat the scanner proposals

The change fuses two invariants of the same tree decoder. It does not
generalize a list scanner, change backward history, introduce an iteration
DSL, or replace lookup lemmas. The previous packets do not discuss this
specific paired code/rank graph theorem.

## 2. Normalize internal constructor equations before inversion

### Source evidence

`ObjectCodeBound.lean` has four inversion theorems:

| Theorem | Lines | Physical lines |
|---|---:|---:|
| `boundCodeRel_atom_inv` | 240-256 | 17 |
| `boundCodeRel_bot_inv` | 258-268 | 11 |
| `boundCodeRel_binary_inv` | 270-297 | 28 |
| `boundCodeRel_quantifier_inv` | 299-311 | 13 |

Each unpacks a certificate, expands the same eight-way `BoundStep`
disjunction, rejects constructor mismatches using `formCode_tag_ne`, and
uses `kpair_inj` to recover payloads. The binary theorem repeats its surviving
payload transport three times, for tags 3, 4, and 5.

### Proposed interface

Prove a model-independent tagged pair equality theorem and instantiate it
with `tag := natV H`, `pair := kpair H`:

```lean
tagged s a = tagged t b ↔ s = t ∧ a = b
```

Then prove a single normal-form equivalence for `BoundStep`:

```
BoundStep H S code result ↔
  ∃ tag payload,
    Allowed tag ∧
    code = kpair H (natV H tag) payload ∧
    BoundPayload H S tag payload result.
```

`BoundPayload` handles the constructor's actual fields, without repeating
the outer tag equality. Its atom case requires natural fields and addition
of their successors; its binary case contains the two certificate membership
facts and their addition relation; its quantifier case is one certificate
membership fact. The bottom case preserves its existing exact code.

A generic tagged-relation inversion theorem then specializes a code already
known to have tag `t` and payload `p`:

```
TaggedRel Allowed Local (tagged t p) result ↔
  Allowed t ∧ Local t p result.
```

The four production inversion theorems can work directly on the remaining
payload condition. Constructor disjointness becomes one reusable boundary,
instead of the same eight alternatives appearing in each consumer.

### Model correctness

This argument uses only injectivity of `natV H` on the finitely many external
tags and injectivity of `kpair H` on arbitrary model elements. It never
claims an arbitrary internal formula code is the quotation of an external
Lean formula. In particular, payloads may be nonstandard internal codes.
Do not introduce an external `Form` parser as a shortcut.

### Validation and limits

`semantic_prototypes/TaggedConstructor.lean` proves the generic tagged pair
and tagged relation inversion theorems over an arbitrary carrier. Both are
axiom-free in Lean 4.32.0. The concrete `BoundStep` normal-form equivalence
and client migrations remain proposed. The current 69-line inversion family
is the measured target, not a promised net saving. Count the helper and
equivalence proofs when measuring the production patch.

This differs from earlier Boolean tag reflection: it normalizes equalities
of set-coded constructors inside arbitrary models, not finite Boolean
dispatch on external Nat data.

## 3. Prove preservation of internal recursion graphs

### Repeated proof that remains after `omega_ind_of_spec`

The following current theorems perform the same mathematical induction,
not merely the same syntax-to-semantics transport:

| Theorem | Source span | Preserved predicate |
|---|---:|---|
| `ObjectArithmetic.addRel_result_nat` | 103-123 | Membership in internal omega |
| `ObjectMultiplication.mulRel_result_nat` | 130-149 | Membership in internal omega |
| `ObjectCodeClosure.closeCodeRel_isFormCode` | 94-112 | `IsFormCodeSem` |

These proof declarations occupy 60 physical lines in total, in addition to
their separately written stage formulas and stage-specification theorems.
At a successor stage each proof obtains an earlier output by totality,
applies its induction hypothesis, and uses graph functionality to identify
the current output with one application of the step function.

### Proposed theorem, with the necessary definability restriction

Let `ThetaG H F a z n` be the existing recursive graph. Let `P` be a predicate
on the ambient model domain. Supply an actual set-theory formula `stage`
and environment `ee`, together with its semantic specification:

```
Sat mem (scons n ee) stage ↔
  ∀ z, ThetaG H F a z n → P z.
```

Assume the existing definability/totality data for the step function `F`,
`P a`, and `∀ x, P x → P (F x)`. Then prove once:

```
ThetaG H F a z n → P z.
```

The proof applies **internal definable induction** to that specified stage
formula. At zero, graph uniqueness identifies the output with the seed. At
successor `n`, totality provides `w` with `ThetaG H F a w n`; the induction
hypothesis gives `P w`; the step closure gives `P (F w)`; and uniqueness
identifies the supplied successor output with `F w`.

The explicit stage formula should initially be a parameter of the helper.
This permits the three current stage formulas to be reused exactly and gives
a small first migration. A later generic syntax constructor can compose the
step graph formula with a formula for `P`; that later layer needs its own
coordinate/renaming specification. Do not make the first patch depend on a
new formula DSL.

### Three immediate instantiations

1. Addition: `F := vsucc H`, `P x := mem x (omegaV H)`, seed's membership
   is the first component of `AddRel`; closure is `omega_succ`.
2. Multiplication: `F a := addValue H a x`, `P` is again internal natural
   membership, and the seed is `vempty H`. Closure uses
   `addValue_rel` followed by the already established addition result
   theorem. This order avoids an import cycle.
3. Closing formulas: `F := allCodeV H`, `P := IsFormCodeSem H`, with
   closure `allCodeV_isFormCodeSem`. The seed can be any internal formula
   code; it need not be an external quotation.

The latter two applications are logically downstream of the first as in the
existing source. No new arithmetic or model assumptions are required.

### Extension: commuting maps transport recursive graphs

For definable `F`, `G`, and `h`, suppose `h (F x) = G (h x)`. The same pattern
proves:

```
ThetaG H F a z n → ThetaG H G (h a) (h z) n.
```

Again, supply a formula representing this exact induction predicate.
If the commutation law holds only on a preserved definable subset, use a
restricted fusion theorem with that subset in its invariant; do not silently
replace the restricted law by a global one.

A first arithmetic client is the left-successor law for addition: both step
functions are successor and `h := vsucc H`. The commutation obligation is
reflexive. Associativity can be approached through a suitable translation
map once its natural-domain commutation law is available. The latter is a
further migration, not a completed or quantified saving.

### Validation and novelty boundary

`semantic_prototypes/IterationGraph.lean` proves preservation and fusion for
an abstract recursion graph with totality, functionality, base, and successor
laws. Its index type is an arbitrary `Index`, with a predicate `Valid`; it is
deliberately not Lean's Nat. The caller supplies `InductionFor` for the exact
stage predicate. Both theorems compiled in Lean 4.32.0 without any axioms.

This proves the reusable logical argument. The adapter to production
`ThetaG`, the formula specifications, and the production client migrations
are not compiled. The report must keep this distinction visible.

The previous proposals contain `omega_ind_of_spec`, which transports an
already supplied predicate through induction. This new helper packages the
additional recursion-graph argument: totality of the previous stage,
functionality at the successor stage, and preservation of the state. It is
also separate from external Nat iterator/scanner invariants.

## 4. Prove unique existence in one internal-code induction

This is a compact companion to the constructor-view proposal.
`ObjectCodeBound.boundCodeRel_total` (324-348) and
`boundCodeRel_unique` (367-405) separately induct over the same eight internal
formula constructors, with separately defined and verified stage formulas.
Prove the stronger single predicate:

```
∀ c, IsFormCodeSem H c → ∃! b, BoundCodeRel H c b.
```

Its explicit first-order stage formula is:

```lean
fEx (fAnd (boundCodeForm 0 1)
  (fAll (fImp (boundCodeForm 0 2) (fEq 0 1))))
```

Here the original code is initially at slot 0. Under the existential binder
the selected output is slot 0 and the code is slot 1. Under the additional
universal binder the competing output is slot 0, the selected output is
slot 1, and the code is slot 2. This is exactly the `ExistsUnique` orientation
`∀ b', R c b' → b' = b`.

For a binary constructor, destruct the two unique child results, use
`addRel_total` to construct the parent value, and prove its uniqueness by
the constructor inversion theorem, the child uniqueness facts, and
`addRel_unique`. Atom, bottom, and quantifier cases are shorter. Existing
public totality/functionality theorems become projections of the single
result, preserving their hypotheses and conclusions.

One can group constructor cases into atom tags 0/1, binary tags 3/4/5, and
quantifier tags 6/7 as a small wrapper around the existing definable induction
principle. This is optional: first measure whether a local shared branch
lemma suffices. Neither the fused unique-existence induction nor its proposed
first-order formula has been production-compiled in this run.

## 5. Renaming-action normalization: a lower-priority option

`AnnotatedSchemaMaps.lean:126-173` lists four exact chains of renaming steps
and manually proves their index maps are `rsep`, `rf1`, `rf2`, and `ri`.
A `Step.indexMap` and a list-composition action theorem would let each
`chainForm` equality follow from one equality of index maps. The cutoff
shift and substitution maps are piecewise affine on Nat, so repeated shifts
at the same cutoff can be collapsed symbolically before binder lifting.

However, these current chain proofs are already very short, and
`rename_comp` is already used. A general normalizer may add more code than it
removes. Recommend this only when another schema or longer chain is added.
The exact four executable lists and their node counts must remain unchanged
for a proof-only refactor. Do not claim this lower-priority option as a
current measurable win.

## Validation summary

Compiler reused read-only: Lean 4.32.0, commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`, matching the pinned project's
toolchain. Successful final logs are the `.check.log` siblings of the three
core `.lean` prototypes and the production-shaped parameterized decoder test.
The production diff passes application checking
only. No production source file was changed and no whole-project build was
attempted.
