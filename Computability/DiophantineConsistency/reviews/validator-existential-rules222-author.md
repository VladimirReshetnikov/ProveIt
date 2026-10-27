# Actual C222 existential term introduction

Author: `controller_certificate`, 26 October 2026. This is the author implementation, complete source review and private fresh leaf compilation receipt. Independent review is separate. Accepted prerequisite sources and objects remain unchanged.

## Frozen sources and results

- `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorExistentialRules222.lean`: 124 lines, SHA256 `3924be0396ae4e13e3b55f0c68d816fca0ca2c6c2f022c82e99cf66720c7f143`.
- `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorExistentialRules222Checks.lean`: 71 lines, SHA256 `0bcf44a39e2d541a912333d094b58ae3f00204b9cb471a984f274d12c4e35b3d`.
- Detailed replay: `reviews/validator-existential-rules222-replay.json`, SHA256 `1efb5d573ce544e83411f7ad244069630de447a3f047851b2318ff7918b2ef42`.
- Main primary: `/tmp/existential-rules222-controller-5fuc7ajz/lib/ZFCinPA/ValidatorExistentialRules222.olean`, SHA256 `b6b0e3dd792ee96f8270442dc988b1d14153c956ba55b5ba22997fd03457be8c`.
- Checks primary: same directory, `ValidatorExistentialRules222Checks.olean`, SHA256 `a90be9d3060a2b52794eefd7e4e20e05c6467ca29b95afc8f8ce8ff6a7b40a11`.

The main passed its first compile, with empty diagnostics, in 3.012 seconds. Final checks passed in 2.250 seconds. All 13 final axiom reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`; peak resident memory was 1,885,724 KiB. The 512 MiB reserve was checked before every invocation, and final recording observed 556,384,256 bytes free.

## Mathematical scope

The sole direct import is actual `ValidatorQuantifierRules222`. The endpoint `ex_term_imp` proves the actual object implication

`encode F 0 s (substs1 set t p) → encode F 0 s (∃p)`

in CProv222 for every internal depth-one typed matrix p and depth-zero typed source term t, with only the original `StreamFree s F` premise. It does not assume the desired inference, an arbitrary proof-translation theorem, a semantic equality, or extra freshness of the interpreted term.

Set z to the actual `TermLabels.term F 0 t` and x to the already represented `eigen F s`. The numerical substitution theorem gives the instance `P = encode F (z∷0) s p`. The target fresh body is `Q = encode F (x∷0) (x+2) p`.

`term_fresh_pair` derives every component of `FreshPair F (x∷0) (z∷0) (x+2) s`. The accepted typed `term_label_avoids` handles both stored labels and fallback1, and excludes source functions or illegal bound lookups through the actual typing guard. Exact singleton cons reasoning handles the bound stacks. Opposite parity and advancing its index by1 establish the apartness of x+2 and s. There is no parity or positivity premise on z, no distinctness requirement on stored labels, and no alleged bound on a numeric cons-list code.

`instance_vac` derives `Vac x P` from the same fresh resources and typed term avoidance. It does not assert `Vac x Q`, self-vacuity, or primitive equality vacuity. No exclusion of the internal auxiliary label in Eind is required.

`instance_primitive_transport` takes the reverse implication of actual Alpha222 under the **same** context `EC(x∷0,z∷0)`. `discharge_cons` produces the curried Eind premise under the old empty context; that old context is truth0 and is discharged with an actual checker witness. Only the valid direction `weq x z → Eind x z` is precomposed, giving `weq x z → P → Q`.

The generic finite helper `ex_intro_relational` permutes the antecedents, combines `Vac x P` with genuine generalization of the implication, and then uses `all_imp_ex` together with actual `ex_equality x z`. This produces `P → ex x Q` without treating a hypothesis as an unconditionally generalizable theorem. The literal encoder EXS equation identifies this fresh-binder result with encoding the source existential at stream x. Actual formula relabelling returns to the original stream s. The numerical substitution identity restores the displayed source term instance.

`ex_term_rule` consumes an actual proof of the instance. `ex_term_rule_under` merely composes the already-proved object implication under any H and therefore requires no `Vac x H`. It does not generalize H. The focused checks expose actual internal History222 proof-code witnesses and cover fallback1, a stored zero, repeated zero labels, and a depth-two matrix under a nested ALL before existential introduction.

The fresh-resource and finite logical helpers use IΣ1; transport explicitly uses IΣ2 through accepted uniform alpha and vacuity. This leaf introduces no new syntax or proof induction. It does not claim arbitrary source-sequent translation, CP/GIC, semantic seed validity, the complete consistency calibration, or HA provability. No old CProv254 semantic result or Eind→weq implication is used. The inherited syntax-only Substitution254 provenance remains as previously accepted.

## Authentication and development record

Approved proposal: `research/c222-existential-rules222-proposal-20261026.md`, SHA256 `9b81d524a1864767c145ac23f9732ec6ff060d4ec1f8b86ac7aab9f578165800`. Read-only cache plan: `research/c222-existential-rules222-cache-plan-20261026.json`, SHA256 `ac8a3931411e906ac3d161670ba72b3bd8abd7dc8a3f675ddbcaed937cdb987d`. Its originally provisional QuantifierRules222 primary is retained as provenance; the actual build uses the subsequently accepted root provider.

That root provider is `/tmp/validator-quantifier-rules222-root-peer-025rx4bk/lib/ZFCinPA/ValidatorQuantifierRules222.olean`, SHA256 `225dc6df8a8b725cf8faba8b562acdd4191e3e0057be23fae30b04828c88f32f`, bound by `reviews/validator-quantifier-rules222-root-replay/ROOT.json`, SHA256 `b3b7f5bc8c294ea7d7fcdc4b0edbe895ea044d59254f4256d3ac9dc80eea820c`. Its source and primary bytes agree with the original frozen author pins.

The private inventory reauthenticates **160 cached prerequisite modules, including 117 Foundation modules, with 511 artifacts and 40 explicit external primary boundaries**. Every selected import list was reconstructed with repeated public/private/meta modifiers supported, and Aesop is retained. No dependency was compiled. The inherited distinction between 20 trace-authenticated added Foundation modules and two historical-primary/later-companion records remains explicit, without a fresh Foundation closure claim.

Private `inputs.json` has SHA256 `f08d530d09f8a23c1873051c2c967855fb9dd101697f5fe60a49614fe352007d`; checkout snapshot is `56c5873debf5b2f48cc3b9c98fcbe85f447cc2a6`. All **734** final source/artifact/parent/compiler/manifest/leaf observations matched, including the retained original author primary. Concurrent unrelated commits do not replace those exact selected-source checks.

The Lean 4.32 compiler has SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`, and the Lake manifest has SHA256 `95e215b005fe9aacc1e5490c781d57e3044d2da5ca452495cfcd0e4eff908665`. All invocations use `-M6000 -j1 -DElab.async=false`, private output paths, and the private symlink overlay plus recorded package roots. The shared project object cache is not in LEAN_PATH; LEAN_SRC_PATH is removed.

All new source/check lines and adapted drivers were read before execution. The main proof passed unchanged on its first invocation. The first check run failed at three simplification calls needing an explicit matrix typing argument for the substitution theorem and at a `1+1=2` normalization. The second check run failed only on explicitly reducing the second stored free label. Supplying the existing cons-successor equality completed it. These repairs changed check proofs, not theorem statements. Both failed snapshots, logs and timings are preserved, including their temporary error-generated `sorryAx` reports; those are not counted as successful audits. The final successful check log has only the 13 standard reports. No accepted source, shared object, shared documentation or Git state was changed.
