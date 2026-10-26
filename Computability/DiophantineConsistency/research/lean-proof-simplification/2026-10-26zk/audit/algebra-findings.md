# Two source-grounded algebra/evaluation simplifications

Review snapshot: `9f35798db4a63c25e435fca14d75931144657d7e`.
All four target source files match the snapshot Git blob hashes recorded by the parent. Both patch files pass `git apply --check` against that snapshot.

## A. Use the affine reflection to share the two Thirteen positivity arguments

Targets: `ThirteenCarrierSoundness.transport_nonneg` (current lines 185-199) and `ThirteenFreshSeed.carrier_exists` (current lines 39-75). Existing API retained.

The common scalar identity is

    y = 1 + 4 [ b m - (1 + b V²) G ].

Prove once, over integers:

    b > 0, G > 0, -2V < y, and the identity imply m > 0.

There is NO sign assumption on V in the new lemma. Suppose m≤0. Since integer positivity gives b≥1 and G≥1, the identity implies y≤1−4(1+bV²). Together with y>−2V this requires 4bV²−2V+3<0. The exact completed-square certificate is

    4(4bV²−2V+3) = (4V−1)² + 16(b−1)V² + 11 > 0.

This contradiction is the new shared arithmetic argument. It does not inspect or change Pell recurrences, sign congruences, quotient witnesses, or norm encodings.

Completeness constructs exactly its old witness: from G=bg and y−1=4be, set m=e+(1+bV²)g. Its affine identity is a ring equality; positivity becomes one invocation of the new lemma. The old hypothesis V>0 is retained to preserve the public theorem signature, although this proof no longer needs it.

Soundness uses an involution that fixes the constant term correctly:

    (m,G,y,V) ↦ (−m,−G,2−y,|V|).

The affine identity is unchanged because |V|²=V². If G<0, then −G>0; the existing bound |y|<2|V| gives −2|V|<2−y. The shared positivity lemma yields −m>0, contradicting m>0. Notice the reflected ordinate is 2−y, not −y: this is distinct from the earlier Pell congruence-up-to-sign abstraction.

### Evidence and scope

- `algebra_prototypes/AffineReflection.lean` is kernel checked with Lean 4.32.0. It contains the new shared lemma and complete replacements with the exact old signatures.
- All three printed axiom sets are `[propext, Classical.choice, Quot.sound]`; there is no `sorry`/new axiom/native-decide shortcut.
- Independent mathematical review by semantic_ideas passed the completed-square and reflection reasoning.
- Patch: `algebra_prototypes/thirteen-affine-reflection.patch`.
- Final source counts including the new shared helper and its documentation: Soundness 290→297 (+7); FreshSeed 217→197 (−20); net **13 lines removed**. This is not a build-time claim.
- All seven affected executable definitions are textually unchanged after removing whitespace/comments.
- Full-module elaboration against existing cache was stopped after a bounded attempt (the first module received SIGTERM; the second was not attempted); this is NOT a successful module build and NOT a complete pinned-closure rebuild: among ten local DiophantineConsistency source modules in the import closure, eight match the cached checkout, while ShortSystem differs and TotalDegreeBound is missing/different there. PellInt and PellHalf90 are external project dependencies. The standalone proof check is independent of these project caches.

### Necessary boundaries / negative examples

- The conclusion for soundness must remain G≥0. With b=1,m=1,G=0,V=3,y=5, its affine identity and |y|<2|V| hold, so G>0 would be false from those hypotheses alone.
- The new positive-carrier lemma needs G>0: b=1,G=0,V=1,m=0,y=1 satisfies the other premises.
- It needs b>0: b=0,G=1,V=2,m=0,y=−3 satisfies the other premises.
- Its use of b≥1 comes from integrality. Over rationals merely b>0 does not suffice: b=1/1000,G=1,V=250,m=0,y=−253 is a counterexample.
- The original positivity/divisibility/Pell hypotheses in the surrounding soundness and completeness endpoints are unchanged.

### Novelty boundary

The novelty audit found no proposed affine reflection/sign-separation mechanism in the 23 placed packets or five current incoming ZIPs. Prior Pell work concerns congruences modulo sign, signed roots, monotonicity and scaled ratios; prior interval APIs may simplify arithmetic syntax but do not identify these two proof obligations as images under the affine involution. Claim this concrete common theorem and its two applications, not a new generic inequality library.

## B. Give the two Jones compilers one concrete finalizer-semantics implementation

Targets: `JonesSyntax.lean` and `ExecutableJones.lean`.

Both modules already use exactly the same `RingVars (Expr σ)`, the same `JonesSyntax.evalExprVars`, and the same closed finalizer formulas. Nevertheless, ExecutableJones repeats five private proofs from JonesSyntax: `eval_rad`, `eval_wt`, `eval_dvsr`, `eval_dvnd`, `eval_marg`.

Minimal proposal: make the five existing JonesSyntax lemmas public and remove the duplicate block from ExecutableJones. Its `eval_withInput` refers to the existing facts with qualified names. The two compiler-specific `eval_syntaxVars` proofs remain separate because their coefficient construction is intentionally different.

This changes no Expr definition, coefficient enumeration, input specialization, literal polynomial or numerical expression. It is orthogonal to the parent's fixed-total-degree enumeration proposal. The existing shared expression-homomorphism baseline does not, by itself, remove this duplicated concrete closure implementation.

### Evidence and scope

- Patch: `algebra_prototypes/jones-shared-evaluation.patch`; complete proposed files under `algebra_prototypes/JonesShared/`.
- Patch applicability passes against the exact snapshot.
- Source counts: JonesSyntax179→179, ExecutableJones300→251; **49 physical lines removed**, no extra helper overhead.
- The data audit confirms all seven JonesSyntax definitions and all fourteen ExecutableJones definitions unchanged after whitespace/comment normalization.
- This patch has NOT been compiler-validated as full modules. Existing private theorem proofs are retained verbatim in the first file, and qualified applications use the same elaborated statements, but that reasoning is not a substitute for a module check. Run the normal pinned `lake build DiophantineConsistency.JonesSyntax DiophantineConsistency.ExecutableJones` before adoption.
- No performance claim. No assertion that exporting these lemmas changes axiom dependencies; compare actual endpoint axioms after compiling if adopted.

### Novelty boundary

The scoped audit found no non-baseline reports/prototypes discussing ExecutableJones/JonesSyntax/RingVars or this five-lemma duplication. Earlier generic row-coefficient homomorphisms are assumed applied. Claim elimination of a second concrete Jones finalizer-semantics implementation, not new generic map laws.

## Files to package

Include `AffineReflection.lean`, its successful `.log`, the two `.patch` files, both metrics JSONs, `source-provenance.json`, `patch-applicability.json`, `jones-data-audit.json`, `thirteen-data-audit.json`, and the dependency comparison if reporting module replay. Do NOT package the abandoned `AffineTransport` draft or the read-only dependency symlinks under `overlay/`. Full modified source files may be copied individually; generated `.olean` outputs are optional and unnecessary.
