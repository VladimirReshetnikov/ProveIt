# Local source60: Beyond252 — mathematical/source review

Reviewer: `review_upstream_reflection`. Scope: all 764 lines of `report.tex`, all251 of `seed_section.tex`, all77 of `negation_proof.tex`, entry/provenance notes, selected certificate implementation, and the current maintained mathematical interfaces. No supplied Python/C++ program, proof assistant, compiler, version query, search, or verifier was executed. No archive-manifest/checksum census was undertaken. Root owns fresh executable reproduction; its results must be attached separately.

## Disposition

Preserve as useful research, with no new state-count record and no new Lean or PA endpoint. I found no fatal mathematical defect in the consistency sandwich, the atom-sensitive full-SIR model, or the clean-scratch negation contract. The model proof is an ordinary set-coded interpretation argument; the numerical and finite-search results remain delivered claims pending root's separate execution evidence.

The package's target is explicitly weaker than the user's project goal: `report.tex:106` asks for a ZFC proof of the nonhalting/consistency equivalence. It does not discharge equivalence **provable in PA**. The report acknowledges this distinction (`report.tex:619` and `seed_section.tex:235`). Treat this as scope, not as authorization to weaken the project goal.

The source pin is ProveIt `a2bf288dead95b653919b86608e3f2cca47552f7`; prior-art pin `c132d7eae8158cd3a9850ea3eb7251158c3dd821` and imported upstream pin `297ab8df7e5de329605c3875b4934643b371a5e3` have separate roles. The paired JSON records exact hashes of the reviewed mathematical text and current interfaces, rather than relying on a supplied checksum manifest.

## Seed sandwich: sound and strictly scoped

`seed_section.tex:63` defines Γ as the universal closures of the current formula, cached formula, and every exposed head of the finite positive prefix of the unshifted Cantor stack. Including the entire prefix is essential. Positive tails descend; the final infinite zero tail contributes only truth. Code1 normalization to Bottom is justified only in the irreflexive model class; quantifying every valuation also handles binders using variable0.

The statement at `seed_section.tex:74` is the correct pair of implications:

```
Con(S + Γ) → Nonhalt(s) → Con(S).
```

For the first implication, choose one common nonempty model of S+Γ, then preserve universal validity of top/cache/all stack entries through every command. Successful MP, failure-to-truth, DROP/NIP, fresh/collision-gated theory roots and GEN are all accounted for. The model is fixed throughout the run. Separate satisfiability of different formulas or truth at a single assignment would not suffice.

For the reverse implication, arbitrary-start completeness really is already available: `EnumSafeStart254.lean:109` has no `Inv` premise. Its padding proof handles arbitrary candidate number and retained data. `NativeTheory254.lean:76` connects the exact native refutation predicate to numerical falsity. Thus the report is not assuming completeness for the augmented theory. It correctly refuses `Halt(s) ↔ ¬Con(S+Γ)` at `seed_section.tex:121`; initial seeds need not remain accessible as added axioms.

The ZFC-valid-seed corollary at `seed_section.tex:128` uses the **same raw membership and identity equality** of a ZFC model to satisfy CP/GIC/IR plus Γ. That is stronger information than abstract equiconsistency and avoids silently moving raw seed formulas to a quotient. The more general L-model suggestion also explicitly requires simultaneous interpretation of the native theory and seeds.

## Two-atom construction: full schema, not a finite-model shortcut

The proof at `seed_section.tex:164` is a credible standard interpretation in a possibly nonstandard set-coded ZFC model M. Atoms have disjoint tags from sets; set tags are injective; all recursive hierarchy/rank reasoning occurs inside M. The interpreted carrier is externally a subset of M's set carrier, so no transitive-model or ω-model assumption is introduced.

For full GIC, translated matrices are ordinary first-order formulas with parameters. Separation isolates inputs with witnesses; Collection gathers witnesses; Separation removes unsupported elements; Replacement on hierarchy ranks bounds the gathered set so its tag belongs to H. This covers the complete original schema, rather than just the finitely sampled matrices.

For CP, a limit stage Hλ contains the chosen p and is R-transitive. The raw subset objects of x are exactly `A ∪ {σ(Z) : Z ⊆ m(x)}`. The inclusion of **both atoms** is necessary and is explicitly present (`seed_section.tex:198`); simply tagging the ordinary powerset would miss them. The displayed subset set and its own tag lie finitely many stages above x, still below a sufficiently high limit λ, providing W ∈R V. Distinct atoms have the same empty predecessor set but remain unequal under actual equality. This yields `Con(ZFC) → Con(S + ¬Ext)` and proves native nonderivability of Ext relative to Con(ZFC).

The construction does not assert a finite model of S, unconditional Con(ZFC), or native underivability of every small newly recognized cycle formula. Finite acyclic/extensional graph evaluations are implementation diagnostics, not the model proof.

## Relation to existing work: do not count semantic startup twice

The current maintained six-constructor `SeedInvariant254.lean:18` proves native `C254` theoremhood (`:40`) and stack goodness (`:53`); `DirtyProgram254.lean:26` still uses exactly that syntactic top/cache/stack invariant. Source60's additional semantic criteria cannot be passed directly as a proof of `DirtyProgram254.Safe`.

However, preserved **source52 already contains the ordinary common-ZFC-model semantic startup argument**, a finite HF decision procedure for its restricted fragment, and 446 additional formula/31 stack recognitions. See `52-roles-research-logical_reduction-foundation_seeds.md:1`, `:83`, and `:280`. Therefore source60 is not the first corpus proposal to replace native theorem certificates by semantic seed admissibility. Its useful additional content is the explicit **general S+Γ consistency sandwich**, the full two-atom strictness witness, and an alternative small certificate implementation. Its five additional formula recognitions relative to the six-constructor legacy recognizer are not five additions beyond source52's recognizer. The source60 Extensionality family has an inner quantifier and is outside source52's quantifier-free/leading-universal fragment.

Existing dirty-root absorption is independently useful for integration: `DirtyRoot254.lean:90` preserves top, stack and cache without a soundness premise, and `DirtyProgram254.lean:46` compares arbitrary dirty starts to the absorbed enumerator. Thus a model-relative invariant can reuse these operational equalities; it needs a new semantic `step_inv/run_inv/halt_step` interface corresponding to `Enum254.lean:176`, not a new binary initializer theorem by fiat. The whole root frame, empty PC, logical tail and physical spares remain independent obligations.

## Negation: exact unbounded arithmetic, no state saving established

The identity `P(t,1)=P(0,t)+2` uses the original dual-Cantor orientation. Prefill two **before** scaling or add eight **after** scaling; confusing those constants changes formula codes. The report's identity is correct.

The existing additive contract is explicit in current `L2Lib254.lean:205` and upstream `ProgLib254.v:409`: pair162 maps `(T,X,Y)` to `(0,0,Y+P(X,T))`, preserving all other registers. `L2Macros254.lean:86` proves `T := T+4Y; Y := 0`. The source proof's drain invariant `Y+P(X,T)`, donor counter termination, and outer decrease of X+T establish the claimed unbounded contract, not merely its finite sample. All three fused macros require clean initial X=Y=0, preserve arbitrary W and other fields, and return clean scratch. The report retains this precondition.

The full replacement still needs an exact changed-program simulation, source occurrence accounting and call-site clean-scratch invariant. Finite structural matching that commutes straight increments is useful executable evidence but does not itself become a Lean program-equivalence theorem. The original exact252 theorem cannot certify altered255 tables. This limitation is explicitly acknowledged.

Reported costs are carefully separated: 281 states in the unmodified Wade controls; 261 after contextual emission; 255 after accepted folds; 5,590 leaves/7,221 guarded cases for prefill versus 5,650/7,311 for direct transfer; unchanged203 shared decoder nodes. The two255 tables' claimed 82,552-step boot is finite evidence about their exact frames. None is a sub252 result, nor can its prospective savings be added to the independent exact250 construction without a single combined table/proof.

## Relational/search scope

The difference-bound reasoning is sound in its stated orientation `b[i,j] : xi−xj≤b[i,j]`: upward cap to infinity and raising a lower negative bound to −K both weaken constraints. Exact guarded postimage inclusion, entry inclusion and natural-counter constraints—not worklist convergence alone—give the inductive invariant. The report explicitly retains one enabled halt case and the same six excluded cases. These zero-root invariants must be re-established for nonzero semantic seeds.

The displacement oracle must track current value as initial value+δ and retain natural-counter invariants. A finite upper bound plus `upper+δ≤0` forces zero; `lower+δ≥1` justifies positive decrement. Existentially forgetting a valid spare suffix is justified only by the imported252 box contracts over arbitrary finite suffixes, not by treating it as arbitrary tape. Those contracts must not be reused for prefix250 without its changed boundary/spare behavior.

The reported complete local families (55,471 compound uniform folds; 266,112 compatible-pair synthesized actions; 280,500 direct255 resumed recipes) have narrowly described eligibility restrictions. Ledger identity/coverage does not replay each symbolic execution. Fuel exhaustion, unsupported symbolic operations and unresolved variable runs are certificate failures, not concrete counterexamples or a state lower bound. The package makes these distinctions. Root's forthcoming replay record must state which components were actually rerun and which checked only existing coverage. I have not verified the numerical counts by execution.

The fixed finite-ZFC-theorem reflection barrier is correctly restricted to each fixed standard finite list; it does not rule out finite class theories or all finite equiconsistent presentations. The independence discussion correctly distinguishes consistency from Σ₁ soundness. No further mathematical defect was found in these scope claims.

## Useful next work

1. For Lean, factor the enumerator invariant over an abstract validity predicate closed under the actual rows, MP and GEN; instantiate both native theoremhood and common-model validity. Reuse dirty absorption unchanged. This is a small concrete bridge, while the binary full-frame proof remains separate.
2. For the user's PA objective, an explicit proof transformation into the native calculus extended by finitely coded universally closed seed axioms is more directly relevant than invoking model completeness. It must work for all internal proof/formula codes; the ordinary semantic argument alone does not supply this.
3. The report's two-atom construction suggests a broader future seed class than ZFC-valid formulas: even the sentence ¬Extensionality is relatively consistent with S and therefore admissible under the sandwich (assuming ConZFC and the operational bridges). This is an inference from the construction, not a delivered small numeric seed or a state reduction. The displayed Ext code is large, so search usefulness remains unmeasured.
4. Prefer completing the exact250 formalization over recompiling the already larger255 controls. If source optimization is revisited, price negation jointly with decoder/register placement and certify one combined literal table, including its actual blank startup.
