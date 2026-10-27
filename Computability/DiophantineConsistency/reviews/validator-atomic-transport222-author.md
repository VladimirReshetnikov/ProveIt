# Actual C222 atomic transport: author receipt

`controller_certificate`, 26 October 2026. This is the root-authorized finite IΣ1 atomic checkpoint, following accepted EindContext222. Complete main/check sources and adapted drivers were read before their bounded private executions and reviewed again after the two diagnostic-only cleanup changes. The packet is frozen; this receipt is an author report, not independent review.

| File | Lines | SHA-256 |
|---|---:|---|
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorAtomicTransport222.lean` | 158 | `9ec5191f298f3b7fe6acd347ab07452f14933f68984b7203d9f5a49a3d6c3198` |
| `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorAtomicTransport222Checks.lean` | 47 | `af0933914dcf6337ff60ae8f3a2c739306f4dd49376a7d39994c25330b684359` |
| `reviews/validator-atomic-transport222-replay.json` | — | `ce6ba2f8a7ea620fc6ddd532eca189afc41fba7fe1d68a84d4e7ff11035baf9f` |
| `research/c222-uniform-alpha-proposal-20261026.md` | 128 | `24ad6ab111843daa5d34a3f6c4cff52956cfc18552ec8b3ebacc8e02e32f13c6` |
| `research/c222-alpha222-cache-plan-20261026.json` | — | `a9073746ac0cef236f51dd128a08ce7d6f15deeeb02adcfa27ba8f25c5f02b49` |

The last three paths are relative to `Computability/DiophantineConsistency`. The proposal/cache plan were saved before source implementation/compilation; their historical read-only status does not describe the later completed leaf. Future uniform Alpha described there is still outside this packet.

## Exact mathematical content

The sole import is `ZFCinPA.ValidatorEindContext222`. All parameters and source terms are internal values of an arbitrary `ORingStructure V` satisfying IΣ1. The actual CProv222 predicate is used throughout, with its actual represented History222 checker.

- `eind_refl` applies actual `Eq_Eind` to actual primitive reflexivity. `eind_symm` applies `Eind_euclid` with pivot a and diagonal Eind(a,a); transitivity uses the resulting symmetry and pivot b. These have no freshness/positivity/distinctness premise.
- `eind_congr` transports both endpoints by three finite indiscernibility steps. `rel_congr` uses actual `Eind_el_l` followed by `Eind_el_r`, preserving member/container orientation. No interpretation of Eind as literal primitive equality is assumed, and arbitrary auxiliary-label collisions are legal.
- `EqUnder h p q` retains the exact same outer h for both implications. `reverse_eind_premise` reverses only its relation premise. `reverse_primitive_premise` explicitly composes `weq(y,x) → Eind(y,x) → Eind(x,y)` before the original body certificate under h. Neither h nor the stack order is changed, and `Eind → weq` is never used.
- `term_eind_under` handles typed set-language terms. Bound variables use the accepted context projection with i<n=len B; free variables use identical free-label interpretation on both sides, including fallback1. The typed function case is impossible because the actual set-language function predicate is false. Total right-stack lookup is sufficient for this finite theorem, so it does not assume len B'=n; both lengths remain required by the proposed uniform alpha/vacuity client.
- `atom_eq_under` derives arity2 from actual set-relation typing, justifies both vector accesses by typed-vector bounds, and uses Eind congruence for symbol0 and membership congruence for symbol1. Both directions preserve EC(B,B'). Fresh-stream parameters do not affect atoms. `atom_forward_witness` exposes the exact numeric `ArithmeticHistory222.value code = conclusion+1` witness.

Focused checks cover repeated zero endpoints, an auxiliary label used as a transported endpoint, the reverse primitive premise under the same old environment context, and the exact typed free-variable fallback1. Axiom audits cover the finite equality/membership certificates, typed atom transport and actual checker witness. This is not a source-formula induction theorem. Uniform alpha, substitution, arbitrary proof translation, full seed validity, tagged CP/GIC calibration, and HA provability remain separate work.

The old Alpha254 source was read only as a guide to the generic typed-term case split and finite context pattern. Its old primitive-weq atom congruence and semantic CProv254 results are not imported or used. The replacement equality-atom argument is derived from the actual C222 Eind resources above.

## Reproducible private execution

Source snapshot: `c271cbbd018fbfc1056532eb157a182c30de665a`. Private overlay: `/tmp/atomic-transport222-controller-0r0d43j3`. Inventory SHA: `1eaa7ab94ed1da9a7e9a36a1f2fc774636bbebdc1552ead2841ae82dc12d57f7`. Exactly **154 cached current prerequisite sources / 117 Foundation modules / 505 prerequisite artifact records / 40 explicit external primary boundaries** were authenticated before execution; no prerequisite source was freshly compiled. The new provider is root's accepted byte-identical EindContext222 primary at `/tmp/validator-eind-context222-root-peer-ml7gi848/lib/ZFCinPA/ValidatorEindContext222.olean`, SHA `5d3a5a6643d1f39df3f9e3f7032da780c95fd56821bfa528a2d8f3427bdad7a7`.

The explicit repeated-modifier import parser retains Aesop and implicit Init. LEAN_PATH contains only the new private overlay and the recorded package provider paths, not the shared project cache. The inherited extra Foundation provenance remains exactly 20 central trace-authenticated modules plus 2 historical successful primary builds with separately observed companions. No Foundation rebuild, cache substitution, shared-object mutation, or whole-closure fresh claim is made.

Both new leaves used pinned Lean4.32.0, `-M6000 -j1 -DElab.async=false`, and private `-o` destinations. The first pair passed. The main then had an unused `if_neg` simp argument removed, and the checks qualified `rel_congr` to prevent Lean also printing an unrelated root declaration with that name. Neither change altered a mathematical statement. Both first-run objects/logs/source snapshots are preserved in the replay record. The final main passed in 3.763s with an empty log; final checks passed in 1.850s with exactly thirteen intended reports, each `propext`, `Classical.choice`, and `Quot.sound` only. There were no failed compiler runs.

Final main object: `1e0dc54a2678ba0a79975390e929f78019e8a1bd63d36e6963d7ba782f576090`. Final checks object: `759b0a5a4c60a54afcf06fef242dde8188683b817bc88ec8cbfe0342835bb12b`. Maximum successful-run RSS: 1,886,436KiB. The recorder reauthenticated 714 compiler/source/artifact/parent/final observations. Free disk after recording was 681,701,376 bytes, above the 512MiB reserve. Complete driver texts, commands, snapshots, timings, logs, development runs and final object pins are in the replay JSON. No frozen source, shared documentation, shared object or Git state was changed.
