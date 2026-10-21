# Shorter checked K215 proofs

The literal 215-state machine and its halting and nonhalting endpoint statements
are unchanged. The [latest Lean check](phase10/README.md) validates the 192-module
endpoint closure, five decoder-prefix modules and both typed endpoint clients.
Eight modules were freshly compiled; 189 providers retain exact phase-nine
transitive source/import bindings. All ten endpoint reports use only
`propext`, `Classical.choice`, and `Quot.sound`; both audits have zero warnings.

| Proof source | Original | Current |
| --- | ---: | ---: |
| Lean dominated implication, core plus adapter | 689,857 bytes | 17,419 bytes |
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

The [latest checkpoint](phase10/README.md),
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
