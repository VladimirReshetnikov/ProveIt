# Proposed actual C222 existential term introduction

Read-only proposal by `controller_certificate`, 26 October 2026. No new Lean source, overlay or compiler invocation is part of this checkpoint. The frozen QuantifierRules222 packet is unchanged. Implementation requires root approval after its independent acceptance.

## Smallest useful endpoint

Propose `ValidatorExistentialRules222.lean` and focused checks, importing only `ValidatorQuantifierRules222`. The essential theorem is an actual object implication, not a theorem with the desired inference supplied as a premise:

```lean
theorem ex_term_imp [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {p t : V}
    (hp : IsSemiformula ℒₛₑₜ 1 p) (ht : IsTerm ℒₛₑₜ t)
    (F s : V) (hs : StreamFree s F) :
    CProv (wim (encode F 0 s (substs1 ℒₛₑₜ t p))
      (encode F 0 s (^∃ p)))
```

All parameters are arbitrary internal elements, not assumed standard naturals. IΣ1 suffices for the fresh-resource and finite logical lemmas; the endpoint explicitly uses IΣ2 through existing uniform alpha/vacuity. It needs no new syntax induction or hierarchy invariant.

Two small clients can apply this actual implication:

```lean
-- Actual proof of the instance gives an actual proof of the existential.
ex_term_rule hp ht F s hs
  (h : CProv (encode F 0 s (substs1 ℒₛₑₜ t p)))
  : CProv (encode F 0 s (^∃ p))

-- An arbitrary hypothesis is preserved by propositional composition.
ex_term_rule_under hp ht F s H hs
  (h : CProv (wim H (encode F 0 s (substs1 ℒₛₑₜ t p))))
  : CProv (wim H (encode F 0 s (^∃ p)))
```

The second client does **not** need `Vac x H`: the already-proved instance-to-existential implication is composed under H. No generalization of a proof with an arbitrary undischarged H is performed. No arbitrary represented context fold or sequent induction is included.

## Actual labels, singleton stacks and all freshness obligations

Set `z = ValidatorEnvironmentLabels254.TermLabels.term F 0 t` and `x = ValidatorQuantifierRules222.eigen F s = alternateStart F s`. The accepted numerical theorem `encode_substs1 hp ht F s` identifies the instance with

`P = encode F (z∷0) s p`.

Set `Q = encode F (x∷0) (x+2) p`. Both stacks have length1, matching the depth-one matrix p. `free p` is instead a depth-zero formula and is used only when an exact opening identity is convenient; the two source objects are not conflated.

The typed set language has no function symbols. A depth-zero term is therefore a free variable; its actual label is a stored F entry or fallback1. Rather than repeating term-case induction, every required inequality can use accepted `term_label_avoids ht F 0 y (by simp) hy (avoid_nil y)`. This theorem already rules out functions and out-of-range bound variables from the typing guard. It imposes no positivity, distinctness or extra term-code bound.

Construct precisely

`FreshPair F (x∷0) (z∷0) (x+2) s`.

Its seven components follow as follows:

1. `StreamFree (x+2) F`: advance `alternateStart_free F s F le_rfl`.
2. `StreamFree s F`: retain the endpoint's original hs.
3. `StreamEnv (x+2) (x∷0)`: every future label exceeds x; use `avoid_cons (avoid_nil _)` and `stream_of_lt (x<x+2)`.
4. `StreamEnv (x+2) (z∷0)`: apply typed `term_label_avoids` to each free-safe label in the new stream, then `avoid_cons`.
5. `StreamEnv s (x∷0)`: use opposite parity from `alternateStart_apart F s`.
6. `StreamEnv s (z∷0)`: apply the same typed term-label lemma to each hs label.
7. `Apart (x+2) s`: swap the endpoints of `alternateStart_apart F s` and advance its x-side index by1. The arithmetic equality `(x+2)+2*i=x+2*(i+1)` is explicit.

None uses a false bound on the numeric cons-list code. The streams s and x+2 have opposite parity; no disjointness of s and s+2 is asserted.

The vacuity required later is only `Vac x P`. `fresh_resources F s hs` supplies `FreeAvoid x F` and `StreamAvoid x s`. Typed `term_label_avoids` gives x≠z, so `Avoid x (z∷0)` follows by the singleton cons lemma. Invoke actual `encode_vac hp F (z∷0) s x` with length1. There is no `Vac x Q`, no `Vac x x`, and no exclusion involving the auxiliary label inside Eind.

## The actual finite C222 deduction

Apply `encode_eq_under hp F (x∷0) (z∷0) (x+2) s` with the preceding resources. Select its **reverse** component under the same original context:

`CProv (eindContext (x∷0) (z∷0) → (P → Q))`.

Use `discharge_cons 0 0 x z`, rewrite the empty context to truth0, and discharge that truth by actual `cProv_truth`. This gives `CProv (Eind x z → (P → Q))`. Precompose `Eq_Eind x z`, in the only permitted direction, to obtain

`CProv (weq x z → (P → Q))`.

No context symmetry, inverse Eind→weq, primitive equality vacuity, or semantic formula truth is assumed. The Atomic/Alpha implementation already supplies the needed indiscernibility transport for both actual equality and membership atoms.

A small IΣ1 finite helper can state:

```lean
ex_intro_relational (x z P Q : V)
  (h : CProv (wim (weq x z) (wim P Q))) (hP : Vac x P)
  : CProv (wim P (ex x Q))
```

Its deduction is fully available from actual RelationalCore222:

1. Finite propositional permutation yields `P → (weq x z → Q)`.
2. Compose `hP : P → wal x P` with `all_mono x` of that implication to obtain `P → wal x (weq x z → Q)`.
3. `all_imp_ex x (weq x z) Q` and the actual theorem `ex_equality x z` yield `wal x (weq x z → Q) → ex x Q`.
4. Compose. The primitive equality witness is consumed in the actual calculus; no equality atom is generalized through an assumed vacuity rule.

The literal encoder equation `encode_exs F 0 x hp.isUFormula` identifies `ex x Q` with `encode F 0 x (^∃ p)`. Formula relabelling from x to s uses the typed closed-bound-context existential, `alternateStart_free` and the original hs. This concludes the requested implication at the original environment and original stream. The exact numerical substitution identity then restores the displayed source term instance.

## Edge cases and focused checks

Planned checks expose the actual internal History222 proof-code witness for `ex_term_imp`, its theorem-rule and arbitrary-H clients, fallback1 from an empty or short free environment, a stored zero label, repeated stored labels, and a depth-one matrix with a nested binder. Only typed matrices/terms are claimed; malformed source0 is not promoted to a meaningful source formula. The fallback1 case still gives x≠1 from the same selector resources. Original seed0 is legal whenever hs holds. No parity restriction is imposed on z or the original stored labels.

Expected source size is roughly 150–190 main lines and 45–60 check lines. This is a finite composition checkpoint; there is no new uniform formula or proof induction. Arbitrary source-sequent translation, source axioms, CP/GIC, semantic seed validity, the final consistency calibration and HA provability remain separate.

## Inspected sources and private-cache plan

The current complete Alpha222, Substitution222, Vacuity222, EindContext222, AtomicTransport222, RelationalCore222, Streams222 and QuantifierRules222 sources were read. Relevant exact `encode_exs` and source typed `TDerivation.exs'` contracts were inspected. The old Instantiation254 and R2Quant implementations were read as source-level guides only. Their semantic CProv254 paths are not imports of the proposed leaf, and old odd-environment hypotheses are not substituted for the actual current resources.

Reauthenticated plan: `research/c222-existential-rules222-cache-plan-20261026.json`, SHA256 `ac8a3931411e906ac3d161670ba72b3bd8abd7dc8a3f675ddbcaed937cdb987d`. Import closure is **160 cached modules, 117 Foundation modules, 511 artifacts and 40 explicit external primary boundaries**. The sole added cached module relative to QuantifierRules' accepted prerequisite closure is frozen QuantifierRules222 itself. No Foundation or other dependency build is needed. All 720 source/artifact/parent/compiler/manifest observations matched; free disk was 584,671,232 bytes. The historical-primary/later-companion distinction is inherited without relabeling.

The new QuantifierRules source is SHA256 `6f1ad9c1d95546d712311a39bd8f4c35ea9f28d8d2d27738320573576e46ae81`; the provisionally authenticated author primary is `225dc6df8a8b725cf8faba8b562acdd4191e3e0057be23fae30b04828c88f32f` in `/tmp/quantifier-rules222-controller-ixe8gflf/lib`. Its independent root review is pending at the time this proposal is saved. Before an authorized build, use the exact accepted root provider and add its receipt pin; no source change or extra dependency refresh is anticipated.

Existing direct semantic dependency pins include Alpha222 `574fa80b4ea7d18d8f1877e848a80f8233c0225c45cb1df66e834da4106158bf`, Vacuity222 `cd02e19ae31785ab5460b8af4e850687ef93c68feb84a1a29a0434872e2244e9`, EindContext222 `828fdba014446b0094ac9ce130f71b5d16205e9ea0814ed752940a46eccb1de5`, RelationalCore222 `3246a40dae816446a560652ff334ad44026752e176e577328622b236855a47a9`, and Substitution222 `db2374e4030d1e6792e7426f59f0699796f9b85f78d66c53a478c488ef34ff61`. Every source and artifact path is recorded in the cache plan.

Any later authorized replay would use the same Lean 4.32 compiler, private symlink overlay, explicit package boundaries, `-M6000 -j1 -DElab.async=false` and a 512 MiB reserve guard, preserving all attempts and source snapshots. This read-only audit did not run Lean, create an implementation, mutate shared objects, change frozen sources or operate Git.
