# Architecture review: K215 at 2ca3a5c16f0876d2cab842056353c03a1ed2f5f0

## Main recommendation: separate semantic libraries from historical machine endpoints

The strongest new simplification I found is in imports, not in the final equivalence theorem. `KEndpoint215.lean` is already 54 lines; its main theorem is a single application of the shared `KEndpoint.blank_halts_iff_zfc_refutation`. `SeedPerm.lean` is already 45 lines, and `seed_iff` is a one-line use of the generalized `EnumPerm.halts_iff`. Proposing these generalizations again would repeat completed work.

Nevertheless the current K215 import closure still includes the old 254 enumerator and its register-program proof. The reason is module-level coupling:

1. `KEndpoint215 -> KEndpoint -> KUpper222 -> ConstructibleChoice -> ZFNative -> NativeTheory254 -> L2Root254`.
2. `KEndpoint215 -> KEndpoint -> KLowerQHyp -> KQ1ZF -> WFTheory -> WFModel -> QuotientZF0 -> Enum254`.
3. `L2Lib222` itself imports `Enum254`, although it never refers to a declaration in the `Enum254` namespace and only needs its underlying `Code254` layer.

These edges are wider than the actual statements used by K215. `ConstructibleChoice` and `KUpper222` use `ZFNative.models_ZF`. `KQ1ZF` uses the generic `WFModel.domain_models_ZF` and associated definitions, not the old numerical-theory equivalence in `WFTheory`. The latter also acquires `InductiveAttempts.ordinary_infinity_of_container` transitively; that dependency must be retained explicitly.

The generated proposal does the following, preserving all existing declaration names:

- Move `ZFNative.models_ZF`, verbatim, to a small new `ZFModels.lean` importing `InternalOrd`. The original `ZFNative.lean` imports it and retains its native-theory and old-program consequences.
- Move the generic prefix of `WFModel.lean`, verbatim, to `WFModelCore.lean`. The original file imports the core and retains the CPGIC-quotient specialization.
- Make `ConstructibleChoice` import `ZFModels`.
- Make `KQ1ZF` import `WFModelCore` and explicitly import `InductiveAttempts`.
- Make `L2Lib222` import `Code254` directly, and update its maintained generator accordingly.

This removes historical machine proofs from the K215 dependency closure while preserving them for their existing callers. It does not remove any existing theorem from the repository. It does not alter the exact table, the enumerator, or the final theorem statement.

### Measured static projection

The included script traverses modules physically under `Computability/BusyBeaver/Lean`; seven imported library names are explicit boundary nodes, and that boundary set is identical before and after the proposed change.

| Measure | Pinned source | Proposed source graph | Difference |
| --- | ---: | ---: | ---: |
| BusyBeaver-local modules in endpoint closure | 180 | 167 | -13 |
| Source lines in that closure | 36,261 | 32,296 | -3,965 |
| UTF-8 source bytes in that closure | 1,989,076 | 1,755,573 | -233,503 |

The byte reduction is about 11.74% in this scoped source closure. This is a source-graph measurement, not an elapsed-build benchmark or a proof-term-size claim. Fifteen old modules leave the closure and two new core modules enter it. The gross removed source volume is 4,199 lines; the net figure above accounts for the new core files and edited import lines.

The proposal patch passes `git apply --check` against the pinned checkout. Its two moved declaration regions are checked byte-for-byte by the generator, with hashes in the JSON receipt. **The integrated patch has not been compiled.** In particular, removing an import can remove an unqualified theorem or an elaborator attribute. A full affected build, both K215 endpoint clients, legacy clients of the two wrappers, and updated source-bound receipts are the acceptance requirements. The script correctly retains `InductiveAttempts`, whose omission would otherwise break `KQ1ZF`.

## A small verified contract abstraction

The repository's block specification has the form

```
Contract p X := forall T S,
  cexec p (T,S,0,0) = none or cexec p (T,S,0,0) = some (X,S,0,0).
```

Thus the generic relation `Returns r x := r = none or r = some x` already describes it exactly. The two useful rules are

```
Returns r x -> Returns (f x) y -> Returns (r.bind f) y
Returns r x -> f x = none -> r.bind f = none.
```

These remove the repeated early-halt branches in `gen_contract`, `mp_contract`, and `program_none`. The remaining proof obligation is the concrete suffix run. The second rule is particularly apt for the final `DROP; NIP; NIP` suffix of a refutation block.

`OptionContracts.lean` proves these rules, their equivalence with the usual partial-result specification, and list-concatenation variants. It imports only `Init`, compiles under Lean 4.32.0, and all eight printed theorem dependency reports are axiom-free. `OptionContracts.log` records the successful output. No ProveIt definitions have been changed. Application requires an adapter for the existing `cexec_append`, or simply using the generic `bind_returns` rule after that theorem rewrites the execution.

This is a proof-maintenance abstraction, not a claim of a dramatic new time reduction. The current `EnumPerm.gen_contract` and `mp_contract` are already much shorter than the older `EnumDom` implementations. Replacing their disjunction case splits is chiefly useful when sharing the compiler across command encodings.

**Semantic proviso:** in this application `none` means that the finite command list reaches the machine's actual halting condition. It does not mean divergence. The permissive contract alone is not a correctness theorem: the separate global invariant is what proves that any early halt implies a derivation of falsity. An always-halting buggy block satisfies the partial-result contract but would fail that invariant.

## A generic finite-progress scheduler theorem

`FairSearch.lean` abstracts the repeated `reach` proof without assuming an unproved fairness principle. Its input `advance` says: from a state between candidates, a finite execution reaches a state between candidates with counter increased by one, or halting has already occurred. For each natural `k` it proves that counter `next(s)+k` is finitely reached or the original state halts. A second theorem composes this with a sufficiently late reset-and-refute candidate.

The generic theorem is axiom-free under Lean 4.32.0 and imports only `Init`; the successful log is supplied. The concrete application must derive `advance` from the existing fetch and `drain` lemmas, and must supply the encoded killer candidate. It does not replace the encoding, drain, or stack-invariant proofs by assumptions in an endpoint. Its benefit is avoiding separate induction proofs for each command vocabulary. It is not yet instantiated in ProveIt.

## Scope and current formal assurance

The pinned `verification/k215/README.md` explicitly states that the checked theorem is external:

```
Halt(K215, blank) iff ZFC has a finite derivation of falsity.
```

Negation gives nonhalting iff syntactic consistency. It also explicitly states that the development does not supply an internal PA proof or a derivation encoded in ZFC's own proof syntax. Therefore a report should not describe its own refactoring as establishing the additional internalization step. The actual endpoints are `KEndpoint215.nonhalting_iff_zfc_consistency` in Lean and `tm215_nonhalting_iff_ZFC_consistent` in Rocq; the latter negates `StandardZFC ⊢TC ⊥`.

The README distinguishes the original fresh builds (204 Lean project modules; 237 Rocq sources and recursive `coqchk`) from the later incremental source-bound simplification checkpoint (192-module current Lean endpoint closure, 197-module union with the five decoder-prefix modules). These are different measurements. My source-graph census counts only the BusyBeaver library directory and should not be presented as contradicting the 192-module full project closure.

## Artifacts and reproduction

- `OptionContracts.lean`, `OptionContracts.log`: standalone checked contract rules.
- `FairSearch.lean`, `FairSearch.log`: standalone checked finite-progress scheduler rules.
- `import_boundary_proposal.py`: generates the proposed overlay, patch and static source graph without modifying the repository. It verifies the pinned Git commit before operating.
- `import_proposal/import_boundaries.patch`: reviewable candidate patch, not kernel-checked.
- `import_proposal/import_boundaries.json`: exact input hashes, copied-region hashes, source-volume measurements, removed-module list and acceptance gates.
- `import_proposal/proposed/`: the proposed new/edited files, included for inspection.

Run the Python script with the ProveIt root and an output directory. Check the patch with `git apply --check`. Compile the standalone Lean files with Lean 4.32.0. The compiler processes in this review were serialized using the shared proof lock.

Primary source paths for citation at the pinned commit: `Lean/BusyBeaver/ZFC/KEndpoint215.lean`, `KEndpoint.lean`, `EnumPerm.lean`, `SeedPerm.lean`, `ConstructibleChoice.lean`, `ZFNative.lean`, `NativeTheory254.lean`, `KQ1ZF.lean`, `WFTheory.lean`, `WFModel.lean`, `QuotientZF0.lean`, `L2Lib222.lean`, all under `Computability/BusyBeaver`; and `Research/ZFC/k225-formal/verification/k215/README.md`.
