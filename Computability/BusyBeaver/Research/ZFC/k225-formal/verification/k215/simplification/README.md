# Shorter checked K215 proofs

The literal 215-state machine and its halting and nonhalting endpoint statements
are unchanged. The [latest Lean check](phase6/README.md) validates the 187-module
primary closure and both typed endpoint clients, using hash-bound predecessor
objects for unchanged modules. All ten endpoint reports use only
`propext`, `Classical.choice`, and `Quot.sound`; both audits have zero warnings.

| Proof source | Original | Current |
| --- | ---: | ---: |
| Lean dominated implication | 689,857 bytes | 30,114 bytes |
| Lean AX routine | 202,222 bytes | 7,563 bytes |
| Lean source data, including stable program | 653,569 bytes | 368,995 bytes |
| Lean site-coverage facade | 107,243 bytes | 14,956 bytes |
| Lean register determinism | 17,209 bytes | 12,988 bytes |
| Lean seed-model proof | 11,711 bytes | 10,710 bytes |
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
Four root interfaces and the retained offset checker passed a separate phase-five
refresh; that historical result is distinct from the current primary check.

The [latest checkpoint](phase6/README.md),
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
