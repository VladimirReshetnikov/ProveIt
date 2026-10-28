# Conditional transfer to the exact current HA sentence

26 October 2026. Author: `circuit_reduction`. **Frozen, fresh main/checks
PASS.** The full 79-line main and 50-line checks, the selected import
interfaces, and both replay drivers were read before execution and the
final source was read again before freezing.

`FoundationHACurrentTransfer.current_iff_translated` takes the explicit
premise `Peano ⊢ classicalSentence 🡘 χ`. It constructs an actual HA proof
of both implications between the exact maintained
`ArithmeticCurrentEquation2011.unsolvabilitySentence` and
`FoundationPAHFSyntax.sentence χᴺ`. The premise is not discharged.

The proof uses the existing full Peano axiom/induction transfer. It takes
the reverse direction of Foundation's existing `imply_doubleNegation`
through the checked intuitionistic proof map, then composes with the
already proved exact current-sentence bridge. The open-context helper
retains its complete finite HA context and arithmetic-axiom support.
There is no new translation recursion, arithmetic axiom, model-truth
argument, target stability hypothesis or copied equation syntax.

`current_iff_neg_translated` specializes an explicit PA premise whose
right side is `∼ρ`. It uses Foundation's existing `neg_doubleNegation`
proof to obtain the literal target `HA.neg (sentence ρᴺ)`. This does not
identify `ρ` with a particular refutation predicate or call that target
an independently defined consistency sentence. Both that identification
and a PA proof of the actual desired source equivalence remain separate.
The imported current binding retains all four ports and exactly one
positive-variable substitution.

| Frozen file | SHA256 |
|---|---|
| `Lean/DiophantineConsistency/FoundationHACurrentTransfer.lean` | `342d4ffaa6a0cfbbdd6466a547d879fab57b64b796f071c1996f5b18565a7e79` |
| `Lean/DiophantineConsistency/FoundationHACurrentTransferChecks.lean` | `29235574c9d5f7042c2073ca476b6947c3f34e58dde81ed202bea51ceee13d9c` |
| [Dependency/replay manifest](foundation-ha-current-transfer-dependency-replay.json) | `c9e316179a0d3cc3fc8884aa84f14112eece06954825f367ac9b310a4f53a984` |

The fresh main object is
`acd5f4033ab0b49b97d788eaec3dcef795de3386873a2acfce9595c7d243cc92`;
checks object is
`9f743e723d80d31d6c6db6b773a8e7fe39058dc287c9afbdb43267622bf591a0`.
They reside only in
`/tmp/foundation-ha-current-transfer-62x8bhu1/lib/DiophantineConsistency/`.
The durable [replay bundle](foundation-ha-current-transfer-author-replay/inputs.json)
retains all source snapshots, all four attempted invocations, logs,
commands, drivers and input hashes.

The private environment reuses 133 authenticated custom modules,
including 85 Foundation modules, from the accepted Narrow and Peano
manifests. Every selected module is reachable from the two direct
imports. All old source/object records in both parent inventories,
including authenticated alternative objects for identical source,
are rechecked; together with inherited traces/receipts and explicit
package boundaries this gives 1,068 pin observations. The 47 external
package/toolchain import boundaries are separately enumerated and hashed.
The exact compiler and package manifests match the accepted Lean 4.32.0
environment. Private symlinks preserve existing objects; no accepted
source or object was overwritten. No Foundation rebuild, wide native
import, full native replay, or umbrella build occurred.

Final commands use `-M6000 -j1 -DElab.async=false` and preserve a 512 MiB
disk reserve. Main passes in 2.77 s with an empty log; checks pass in
2.17 s with ten reports containing only `propext`, `Classical.choice`,
and `Quot.sound`. This metatheory axiom report does not add rules to HA.
The checks preserve the arbitrary source-PA premise, both directions,
the literal negative target, arbitrary open contexts, and the bottom
specialization of the existing negation proof.

Two rejected development main runs are retained. The first required
fully qualifying the existing connective-homomorphism rewriting lemmas;
the second required simplifying the goal before applying the already
constructed negation derivation. Only proof presentation changed.
Neither failed run is accepted, and neither changed a theorem statement.
All source, dependency and final-object hashes passed the final audit.
