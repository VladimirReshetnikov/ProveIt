# Actual C222 uniform environment alpha: author receipt

`controller_certificate`, 26 October 2026. This completes root-approved proposal B after the independently accepted AtomicTransport222 checkpoint. The complete new sources and adapted execution drivers were read before execution, and the final sources were read again before this receipt. The two sources are frozen. This is an author report, not independent review.

| File | Lines | SHA-256 |
|---|---:|---|
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEnvironmentAlpha222.lean` | 297 | `574fa80b4ea7d18d8f1877e848a80f8233c0225c45cb1df66e834da4106158bf` |
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorEnvironmentAlpha222Checks.lean` | 62 | `1a3655e6100390c337414a2ff6fcfa78c49e6184ea4849e8fe360741128010e2` |
| `reviews/validator-environment-alpha222-replay.json` | — | `333cd5571624fd3a269d2e4d82f6cf60f827dc4b2669e3a570e33041fd8c0c41` |
| `research/c222-uniform-alpha-proposal-20261026.md` | 128 | `24ad6ab111843daa5d34a3f6c4cff52956cfc18552ec8b3ebacc8e02e32f13c6` |

The last two paths are relative to `Computability/DiophantineConsistency`. The earlier proposal was saved before implementation; its historical prospective language is retained unchanged.

## Mathematical interface and limitations

The sole import is `ZFCinPA.ValidatorAtomicTransport222`. All source codes and six environment parameters are arbitrary internal values of an `ORingStructure V`. Finite transport and stream arithmetic use IΣ1. The uniform formula theorem explicitly requires IΣ2.

`FreshPair F B B' s t` states that both future streams `s+2*k` and `t+2*k` avoid every free label, including fallback1, both represented bound stacks, and each other. It does not silently require positive or distinct stored labels, fixed stream parity, or freshness of an Eind auxiliary label. `freshPair_next` establishes the exact pushed-stack and advanced-stream invariant: the next stream avoids its own former head by strict growth and avoids the opposite head by `Apart`.

`cross_body_vac` uses actual C222 `encode_vac` with source typing at depth `n+1` and both stack lengths equal to n. It obtains the two opposite-body vacuity certificates. `encoded_binder_steps` separately derives both old-context vacuity certificates from `eindContext_vac`. There is no assumption that a binder is vacuous in its own body or that a formula is vacuous in its own numeric code.

The reverse universal step retains exactly `eindContext B B'`. It explicitly precomposes `weq(t,s) → Eind(t,s) → Eind(s,t)` before the reverse body certificate, then applies the actual relational universal rule. It neither swaps the old context nor assumes `Eind → weq`. Existential transport uses the literal encoded negation/universal definition, with derived negated-body vacuity.

The full invariant universally quantifies n, F, B, B', s and t, and concludes both CProv implications under the same represented context. Its Π2 definability is proved from the fixed encoder/context graphs, Σ1 actual proof-existence predicate, Π1 freshness predicate and typed syntax predicate. `encode_eq_under` passes that explicit definability proof to `InductionOnHierarchy.order_induction_sigma Π 2`; it does not invoke induction on an arbitrary Lean predicate. Every recursive source constructor has a checked smaller numeric code. Atomic cases use the accepted typed arity-two transport; the set language has no function-symbol case to misuse the fallback branch.

`encode_formula_alpha` discharges the actual empty-stack context using CProv truth. `encode_malformed_eq_under` separately covers the output-zero malformed branch; it does not claim source0 is a typed formula. `encode_alpha_witnesses` exposes both actual internal numeric `ArithmeticHistory222.value code = conclusion+1` witnesses, without assuming that any parameter or witness is standard Nat.

Focused checks cover malformed0, impossibility of coincident streams under Apart, reflexivity without an impossible Apart premise, two successive binder pushes, the reverse ALL direction under the same old context, and the actual reverse numeric proof witness. All fifteen intended audits have only `propext`, `Classical.choice`, and `Quot.sound`.

The old EnvironmentAlpha254 source was read only as a source-structure guide. No old semantic Alpha254 or CProv254 theorem is imported. This packet does not prove source substitution, arbitrary proof translation, full seed validity, CP/GIC calibration, or an HA derivation. The final HA-provability target remains separate.

## Private execution and provenance

Source snapshot: `bae83b979946ba092ff74efb9c7d46f58e62abf7`. Private overlay: `/tmp/environment-alpha222-controller-ycur20a1`. Input-inventory SHA: `1c7f8cd4bc739e12f0ded7e74d74769f6dc29167ea50a2331f78e0d8d72a154a`.

Exactly **155 cached current prerequisite sources / 117 Foundation modules / 506 prerequisite artifact records / 40 explicit external primary boundaries** were authenticated. The added provider is root's accepted AtomicTransport222 primary at `/tmp/validator-atomic-transport222-root-peer-qocsrsy8/lib/ZFCinPA/ValidatorAtomicTransport222.olean`, SHA `1e0dc54a2678ba0a79975390e929f78019e8a1bd63d36e6963d7ba782f576090`, bound to root record `a44f791b28bc6822f4d54d9161eb413347839eadf4c39cb45e23384c32e4f7df`.

No prerequisite or Foundation source was compiled. The inherited extra Foundation subset retains its precise distinction: twenty central trace-authenticated modules and two historically successful private primary builds whose companions were separately observed later. The repeated-modifier import parser includes Aesop and implicit Init. LEAN_PATH contains only the private overlay and the recorded explicit package paths, excluding the shared project cache.

Both new leaves used pinned Lean4.32.0 with `-M6000 -j1 -DElab.async=false` and private output paths. The main passed its first run in 13.998766s with an empty log. Initial checks failed solely because an `omit` annotation removed the IΣ1 instance actually referenced by Apart. That failed check log contains a `sorryAx` diagnostic and is explicitly excluded from accepted evidence. Its source snapshot, command and diagnostics are retained. Removing only that unnecessary annotation produced the final checks PASS in 2.046341s, with exactly fifteen standard-only reports and no other diagnostics. The main remained unchanged; there was no cap increase or mathematical statement change.

Final primary objects:

- Main: `0e905fe0fb08c3052ecfa8c46ccfc4d881e7590b677b36b5eebd8777823280e1`, 586144 bytes.
- Checks: `507d694d356ba7848ec1f0e226524924ee63d92b68982b4f1d6bbedeed2b3a97`, 67448 bytes.

Maximum successful-run RSS was 1,915,252KiB. The recorder reauthenticated all 716 compiler/source/artifact/parent/final observations. Free disk after recording was 569,864,192 bytes, above the 512MiB reserve. Complete driver texts, commands, source snapshots, timings, logs, development attempts and final object pins are preserved in the replay JSON. No frozen prerequisite, shared object, shared documentation or Git state was changed. Work stops at this alpha checkpoint pending review; no subsequent substitution or proof-translation implementation is included.
