# Shorter checked K215 proofs

The literal 215-state machine and its halting and nonhalting endpoint statements
are unchanged.

The [phase18 combined Lean check](phase18/README.md) passes for shared macro
proofs and the upstream Profile/syntax cleanup. Across 199 selected project
modules it removes 683 Lean lines / 27,373 bytes. Producer retirement and its
companion repair bring net maintenance savings to 756 lines / 31,070 bytes.
The endpoint imports four reference modules and grows from 174 to 178 modules.
All retained assumption profiles match exactly; independent result review and
evidence capture pass. The [phase17 record](phase17/README.md) retains its accepted scope.
The table below retains its accepted source comparisons through phase16.

| Proof source | Original | Checked through phase16 |
| --- | ---: | ---: |
| Lean dominated implication, core plus adapter | 689,857 bytes | 16,826 bytes |
| Lean generic core plus Lukasiewicz (phase-twelve comparison) | 42,454 bytes | 18,243 bytes |
| Lean shared derived/profile sources (phase-thirteen comparison) | 87,279 bytes | 75,163 bytes |
| Lean recursion hierarchy pair (phase-fourteen comparison) | 33,002 bytes | 24,329 bytes |
| Lean quotient construction and adapters (phase-fifteen comparison) | 76,405 bytes | 52,558 bytes |
| Lean AX routine | 202,222 bytes | 7,563 bytes |
| Lean source data, including stable program | 653,569 bytes | 368,995 bytes |
| Lean site-coverage facade | 107,243 bytes | 14,956 bytes |
| Lean register determinism | 17,209 bytes | 12,988 bytes |
| Lean seed semantics, both modules | 19,547 bytes | 13,793 bytes |
| Rocq dominated implication | 921,691 bytes | 22,673 bytes |

The main changes share mathematical arguments instead of repeating their
instances. Offset-bisimulation symmetry eliminates sixteen reverse-certificate
modules; guarded implication lemmas avoid expanded substitutions; one general
enumerator theorem covers both starts; symbolic execution proves its block
contracts; and the AX routine composes a finite word of existing macro contracts.
A general run-prefix lemma removes a duplicated segment induction. Ordinary
bisimulation removes the zero-offset layer; shared tag and bounded-quantifier
lemmas shorten semantic proofs. Through phase five the import closure shrank
from 204 to 184 project modules. Phase six adds normalized correspondence,
stable program data and transition-lookup transport, for 187 modules. It checks
1,426 normalized entries rather than the earlier ordinary 2,240, preserving the
512-step decoder and all 4,751 leaves. The full source partition is 375,335 bytes
in 19 files; its additional generic normalized checker is 6,365 bytes.
Phase seven replaces the dominated-implication deduction theorem with two
pointwise lifts and removes the unused distribution derivation. Its source drops
from 517 to 454 lines. Four root interfaces and the retained offset checker pass
a [fresh five-client audit](phase7/legacy/README.md) against all 202 providers;
the 15 legacy modules retain their exact direct-dependency bindings.
Phase eight abstracts numerical coding out of the implication proof and shares
one semantic equivalence between both seed directions. The two proof groups
shrink from 45,316 to 35,851 bytes, counting both the new core and its adapter.
Its [legacy check](phase8/legacy/README.md) retains all 15 extra interfaces and
reruns the five-client audit against 203 current providers.
Phase nine shares the Home return proof and checks exact source-to-zipper decoder
entry. Its nine fresh site batches retain all 6,176 outcomes and take 16.41 minutes,
against a historical 27.49 minutes. Phase ten adopts the generic 52-step derivation
and six compatibility lemmas, saving another 4,639 bytes and 51 lines in the core.
Phase eleven removes the temporary seed wrapper and inlines two single-use aliases,
saving another 1,016 bytes and 43 lines. Its self-contained producer reproduces the
checked source; retiring two unused templates brings the maintained core, producer
and template reduction to 6,463 bytes relative to phase ten.

Phase twelve separates the semantic interfaces from older clients, reducing the
endpoint closure from 192 to 179 modules and its selected sources by 233,503 bytes.
A separate compatibility check preserves the old model/native interfaces. The
seven edited or new proof sources grow by 491 bytes; their bodies are unchanged.
Phase thirteen shares the numerical and unrestricted implication derivation,
removing 24,211 bytes and 410 lines across the generic-core/Lukasiewicz pair.
The generic core grows by 423 bytes to export K, Peirce and S, while the unrestricted
module becomes a short adapter with its complete Tarski bridge preserved. The
179-module endpoint's selected sources fall to 2,105,228 bytes. Its old model/native
interfaces pass a separate 68-module check with two clients; no module is added.

Phase fourteen shares propositional, quantifier and atomic-rewriting proofs
between the ordinary and equality-restricted named calculi. Its single-use wrapper
is inlined. The profile contracts use transitive containers directly, removing the
duplicate `KProfileTC` module and its generator. Lean sources shrink by another
12,116 bytes and 243 lines; the retired generator removes 3,067 bytes and 71 lines.
The 178-module endpoint selects 2,093,112 bytes. Primary and compatibility checks
cover 198 distinct project modules and preserve all endpoint assumptions.

Phase fifteen abstracts relation-parametric transfinite recursion and reuses it
for the cumulative and operation hierarchies. Quotient syntax is shared without
strengthening the weak model hypotheses; quotient-environment equality replaces
repeated congruence inductions. A small PowerSets module removes unrelated imports,
and the dense proof uses one stopped-or-synchronized invariant. Nine Lean files
shrink by 11,809 bytes/283 lines; the synchronized producer grows by 1,307 bytes/12
lines, for a net maintenance reduction of 10,502 bytes/271 lines. The 176-module
endpoint selects 2,052,142 source bytes, 40,970 fewer than phase14. This dependency
saving and the physical-file saving measure different scopes.

Phase sixteen replaces the parallel quotient developments by one `QHyp`
construction. Its CP/GIC adapter supplies the existing weak interface; native
axiom and collection proofs are shared without adding hypotheses. Removing twelve
unused forwarding helpers and inlining the sole trace instance reduces the thirteen
Lean sources from 76,405 to 52,558 bytes. Including the retired generator, the
maintenance reduction is 29,837 bytes/622 lines. The endpoint selects 2,028,295
source bytes. The successful primary and compatibility checks bind 199 project
modules and retain all exact endpoint/API profiles and 6,176 inherited site outcomes.

Phase seventeen preserves the twelve-wrapper and trace cleanup while combining
Claude Code's frozen main `140d832128` with checked parent `d3ff74a6fa`. The static
89-file Lean comparison across variants removes 1,252 lines and 1,522,387 bytes;
this source-review measure does not claim compilation of every variant. Local
cleanup accounts for 18 Lean lines/690 bytes and 15 producer lines/488 bytes.
The successful 213-provider check preserves all thirteen earlier clients, adds
the direct-seed client and checks all nine 215 site batches fresh. The selected
closure and physical-file savings measure different scopes and are not additive.

The [latest accepted checkpoint](phase18/README.md),
[seventeenth checkpoint](phase17/README.md),
[sixteenth checkpoint](phase16/README.md),
[fifteenth checkpoint](phase15/README.md),
[fourteenth checkpoint](phase14/README.md),
[thirteenth checkpoint](phase13/README.md),
[twelfth checkpoint](phase12/README.md),
[eleventh checkpoint](phase11/README.md),
[tenth checkpoint](phase10/README.md),
[ninth checkpoint](phase9/README.md),
[eighth checkpoint](phase8/README.md),
[seventh checkpoint](phase7/README.md),
[sixth checkpoint](phase6/README.md),
[fifth checkpoint](phase5/README.md),
[fourth checkpoint](phase4/README.md),
[third checkpoint](phase3/README.md),
[second checkpoint](phase2/README.md), and
[first checkpoint](phase1-README.md) retain their respective sources, kernel
records, generator controls, independent reviews and failed attempts. The
[original full-build baseline](../README.md) and attribution are preserved.
Subsequent checks are incremental and keep every reused source/dependency/object
binding explicit. The endpoint is an external proof-assistant theorem; this work
does not supply an internal PA derivation or a minimum-size theorem.
