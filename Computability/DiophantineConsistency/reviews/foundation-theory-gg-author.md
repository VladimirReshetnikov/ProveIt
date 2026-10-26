# Finite-theory negative translation: author checkpoint

Author: `circuit_reduction`, 2026-10-26. Both new sources were fully read and freshly compiled sequentially with Lean v4.32.0, `-M6000 -j1`, and `Elab.async false`. Both final builds returned zero. The main log is empty; the checks log has eight standard-only axiom reports and no warnings. No vendor source, existing module, shared object, umbrella import, equation, or graph was changed.

## Exact theorem

`DiophantineConsistency.FoundationTheoryGG.theory_godelGentzen` proves:

```lean
{L : Language} → [L.DecidableEq] → {Λ : Hilbertᵢ L} →
{T : Theory L} → {φ : Sentence L} →
T ⊢ φ → T.ToTheoryᵢ Λ ⊢ φᴺ
```

`theory_intuitionistic` specializes the target to Foundation's actual `𝗜𝗻𝘁¹` calculus, containing ex falso and no unrestricted excluded-middle rule. The more general result also admits the minimal target, as checked. The theorem is about existence of a proof, as requested by the user; the implementation additionally supplies the proof-tree map `theoryProof`.

The finite helper invokes the already existing `Derivation.gödelGentzen` exactly once. It discharges the extra negated conclusion with the existing negative-translation negation identity. `theoryProof` retains the original proof's complete finite axiom list, after embedding and translation, and verifies that each translated axiom belongs to `Theory.ToTheoryᵢ`. It does not appeal to semantic completeness, model standardness, an assumed translated theorem, or an assumed target subset. The original GG recursion is not duplicated.

This target is the **image of the supplied axioms under negative translation**. It has not been identified with conventional HA. Arithmetic equality/order/base axioms, arbitrary induction, the bridge between Foundation and PAHF arithmetic syntax, and stability of the actual no-witness/refutation target remain separate. The exact215-machine and native-equation internal arithmetic equivalence also remain open; no statement in these modules claims them. See `ha-existing-foundation-api-audit.md` for the inspected existing240 calibration and precise API gaps.

## Focused checks

The checks exercise an axiom from an arbitrary theory, a real two-axiom conjunction, duplicate assumptions in a finite list, the image of the empty theory, translation of an actual empty-theory proof of excluded middle, the exact retained context and its length, and the minimal logical target. The excluded-middle check proves only its negative translation, not unrestricted excluded middle in intuitionistic logic. The same source context length is preserved even when assumptions are repeated.

All eight reports use only `propext`, `Classical.choice`, and `Quot.sound`. These are metatheoretic dependencies inherited from the Foundation infrastructure; the target remains the explicitly defined intuitionistic derivability relation. There is no `sorry`, new axiom, `native_decide`, or semantic reflection rule in the new sources.

## Authenticated prerequisite reuse

The source checkout is `/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation`, commit `32e1a0956a8622fad067328ca1959729a7634428`. Its standalone toolchain pin is v4.31.0. However, the central parent project had already compiled the required complete **59-module custom GG import closure under v4.32.0**. Every corresponding build trace records exactly Lean `4.32.0`, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

Before loading these objects, the current 59 source files were hashed using the compiler's own `Lake.computeFileHash` text mode and compared to each trace's recorded source hash. All 236 `.olean`, `.olean.server`, `.olean.private`, and `.ir` companions were hashed in binary mode and compared to the recorded trace outputs. Every comparison passed. SHA-256 pins for all sources, traces and companions were also saved and rechecked after the fresh leaf builds. Central and current parent-project toolchain/manifest bytes match. Mathlib and other packaged dependencies are reused under that matching manifest; this is not a fresh replay of those libraries or all Foundation sources.

Private overlay: `/tmp/foundation-theory-gg-5j7xbql2`. It contains only private links to the authenticated 59-module cache and the two new fresh objects. No object in a shared cache was overwritten. Exact commands, compiler hash, source/object/trace pins, hash-driver source, final logs and prior failure-log hashes are in `foundation-theory-gg-dependency-replay.json`.

The first main attempt had local coercion and universe-elaboration failures. The first checks attempt had a coercion failure and an unused typeclass warning. These were corrected without changing the target theorem; their logs remain explicitly failed. Only the final clean main/check objects are accepted by this author checkpoint. No broad Foundation build was launched.

## Frozen pins

| Artifact | SHA-256 |
|---|---|
| `FoundationTheoryGG.lean`, 61 lines | `e45262d232cf99f97ee2595f422b8f8afd7306e05eb6f4c8fcdb7c712f8cc2b0` |
| `FoundationTheoryGGChecks.lean`, 76 lines | `c5437204a5eac0e525af860b7f55f21a50d99f16bb12cceec82cc5b3219aa850` |
| Fresh main object | `2e3527392649a97e4fe31c758cd620e88f42ae99719844146ef71cb4fc347762` |
| Fresh checks object | `d081efaa2b4037dcb18fd0382a739ed9db67a699ceb285636d84d17a9da8918a` |
| Dependency/replay JSON | `c87217d0acc6cea36ad2598e2a3896e770322402a6c3a79dda8cd1db4c33ba42` |

This is the author checkpoint. Independent review and replay remain separate.
