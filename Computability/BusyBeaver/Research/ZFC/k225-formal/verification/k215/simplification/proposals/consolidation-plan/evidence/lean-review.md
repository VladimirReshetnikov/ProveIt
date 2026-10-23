# Lean K215 audit and checked current-source contribution

Pinned revision: cbf94cb552a3b49509e0eee80e7455d4eb5974c6.

## Main finding

The large architectural improvements already exist: generic KEndpoint,
positive-progress KSim, one-direction normalized source bisimulation,
Home acceleration, direct FullSeed on the original model, shared quotient
syntax, and relation-parametric transfinite recursion. Recommending these as
new would be stale. Current KEndpoint215 itself is already a short composition.

An unadopted, concrete opportunity is to derive quotient Replacement from the
already-proved quotient collection theorem, using literal equality. This is
not a new mathematical idea in this session: it is proposed explicitly in
`simplification/proposals/collection-first` and
`simplification/proposals/native-replacement`. The latter's sources were marked
uncompiled. We now implement it against current HEAD and compile the full
generic-endpoint/lower chain plus compatibility clients.

## Actual source paths

All paths below are under `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`:

- `KQ1Collect.lean`: `quotient_collection` covers all actual Form matrices under
  arbitrary quotient parameter valuations. It already handles raw representative
  lifting and output/input equivalence.
- `KQ1Replacement.lean` (142 lines, 6,640 bytes): old adapter repeats a guarded
  raw matrix, invariance, representative functionality, interpreted image, and
  quotient descent. Its old public helper APIs are preserved.
- `KQ1ZF.lean`: uses the Replacement endpoint for its repl field and for
  `ordinary_infinity_of_container`.
- `InductiveAttempts.lean` (347 lines, 17,819 bytes) imports
  `QuotientReplacement.lean` (70 lines, 3,686 bytes). That transitive edge keeps
  the old raw Replacement proof in the closure if only KQ1ZF's direct call is changed.

## Delivered implementation

Directory: `/workspace/scratch/2536eb8a7bd2/prototypes/lean_native`.

Four production files in `overlay/`:

1. `KQ1ReplacementNative.lean` (74 lines, 3,526 bytes): generic exact-image lemma,
   actual-Form domain guard, native Replacement theorem, and the two quotient
   endpoint wrappers with exact old types.
2. `InductiveAttemptsCore.lean` (320 lines, 16,239 bytes): byte-preserved generic
   finite-attempt proof, excluding the CP/GIC facade import and specialization tail.
3. `InductiveAttempts.lean` (37 lines, 1,934 bytes): compatibility facade importing
   the core and retaining the original specialization tail byte-for-byte.
4. `KQ1ZF.lean`: import the core and native module, and use native Replacement
   at the two previous call sites. Public theorem statements are unchanged.

No public original Replacement declarations are removed. This avoids forcing
downstream clients of interpreted/raw helper APIs to change.

## Mathematics and precise hypotheses

For an arbitrary membership relation m, relation r, and domain a, collection of
the guarded relation m(x,a) AND r(x,y) supplies a set b with:

1. m(y,b) implies some x with m(x,a) and r(x,y).
2. If m(x,a) and some output exists, an output z belongs to b.

Assume only partial functionality on a: m(x,a), r(x,y), r(x,z) imply y=z.
Then m(y,b) iff there is x in a with r(x,y). The forward direction is support;
the reverse uses coverage and equality. No totality, extensionality, inhabitedness,
choice, or global semantic comprehension is required for this elementary lemma.

The actual formula adapter uses
`guardForm phi = fAnd (fMem 0 2) (rename guardRename phi)` with
`guardRename(0)=1`, `guardRename(1)=0`, `guardRename(k+2)=k+3`.
Collection's matrix convention is input slot 0/output slot 1; Replacement's
`relOf` convention is output slot 0/input slot 1. The checked renaming therefore
must swap those slots and skip a newly inserted domain parameter.

Renaming acts on phi itself, because native quotient collection already handles
native equality. There is no second equality-free translation in the new proof.
All actual collection premises remain Form-indexed. The old QHyp assumptions
are unchanged.

## Measured effects

Static selected-source closure of literal `KEndpoint215`:

- 174 -> 173 project modules.
- 1,752,650 -> 1,744,292 UTF-8 source bytes: -8,358 bytes.
- 37,648 -> 37,483 physical lines: -165 lines.

Removed from active closure: InductiveAttempts, KQ1Replacement, QuotientReplacement.
Added to active closure: InductiveAttemptsCore, KQ1ReplacementNative.

Without the InductiveAttempts split, the change would instead add 3,544 bytes,
74 physical lines and one module. This is a useful concrete lesson: changing
the called theorem does not eliminate an imported proof lane.

Whole maintained affected source, including compatibility, grows by 3,902 bytes
and 84 physical lines. Do not call the result a repository-wide line reduction.
Its advantage is a simpler live proof/dependency route, with old interfaces
available for separate continuity checks. No build-speedup is claimed.

## Fresh validation

`build02` is final. Lean 4.32.0 compiled 107 project modules plus two audit
clients from fresh project objects; 109 successful processes, total compiler
time 55.58655 seconds. Includes `KEndpoint.blank_halts_iff_zfc_refutation` and all
affected semantic descendants, followed by old Replacement/InductiveAttempts
facade continuity. All compiler exits zero. Both audit clients have no warnings
or errors. Dependencies have 15 existing warnings. No sorryAx occurs.

Exact assumption reports:

- `exact_image`: none.
- `sat_guardForm`, `replacement_of_collection`: propext.
- Both new quotient endpoints, both old quotient endpoints,
  KQ1ZF.zf_consistent, and KEndpoint.blank_halts_iff_zfc_refutation:
  propext, Classical.choice, Quot.sound.

Typed clients establish identical theorem types; equality of proofs by `rfl`
uses Lean proof irrelevance and is not an algorithmic equality or speed claim.
Old nine-declaration Replacement API checks pass. All generic and CP/GIC
finite-attempt proof bodies are unchanged, verified by source comparison.
The generated patch passes `git apply --check` on the pinned repository.

Not checked: physical machine-specific site/source/boot certificate closure and
literal KEndpoint215 after the overlay. This is a freshly checked generic
endpoint component, not a newly certified full K215 endpoint. Existing historical
full-machine receipts remain separate and cannot be reinterpreted as checking
these changed imports.

## Relevant previous proposals

- `proposals/native-replacement/report.tex`, sections 2-3, already gives guarded
  image, Form adapter, and warns about InductiveAttempts' transitive dependency.
  It proposes lightweight replacement cores; our minimal generic finite-attempt
  split is a concrete way to close that import boundary.
- `proposals/collection-first/.../CollectionFirst.lean` supplies the earlier
  standalone exact-image argument and proposes wider Separation reordering.
  We restrict adoption to Replacement because collection already depends on
  Separation's valuation-lifting infrastructure. This keeps the import graph acyclic.
- `proposals/common-macros/.../KSeedFunctional.lean` already implements functional
  seed normalization. Its support cost currently outweighs local source savings,
  so it is not the recommended next size-focused change.

## Reporting recommendation

Lead with semantic interface reuse, then explain the exact implemented result.
State current-source measurements, compatibility growth, and the full-machine
validation boundary side by side. Avoid implying that the checked Lean theorem
itself is an internal ZFC proof: the repository's metatheoretic calibration and
the still-open internal PA endpoint retain their existing status.
