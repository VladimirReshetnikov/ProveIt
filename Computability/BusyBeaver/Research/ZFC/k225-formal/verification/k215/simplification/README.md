# Shorter checked K215 proofs

The literal 215-state machine and its halting and nonhalting endpoint statements
are unchanged. The [latest Lean check](phase5/README.md) validates the 184-module
primary closure and both typed endpoint clients, using hash-bound predecessor
objects for unchanged modules. All ten endpoint reports use only
`propext`, `Classical.choice`, and `Quot.sound`; both audits have zero warnings.

| Proof source | Original | Current |
| --- | ---: | ---: |
| Lean dominated implication | 689,857 bytes | 30,114 bytes |
| Lean AX routine | 202,222 bytes | 7,563 bytes |
| Lean source data | 653,569 bytes | 432,131 bytes |
| Lean site-coverage facade | 107,243 bytes | 14,916 bytes |
| Lean register determinism | 17,209 bytes | 12,988 bytes |
| Rocq dominated implication | 921,691 bytes | 22,673 bytes |

The main changes share mathematical arguments instead of repeating their
instances. Offset-bisimulation symmetry eliminates sixteen reverse-certificate
modules; guarded implication lemmas avoid expanded substitutions; one general
enumerator theorem covers both starts; symbolic execution proves its block
contracts; and the AX routine composes a finite word of existing macro contracts.
A general run-prefix lemma removes a duplicated segment induction. Ordinary
bisimulation removes the zero-offset layer; shared tag and bounded-quantifier
lemmas shorten semantic proofs. The import closure shrinks from 204 to 184
project modules. Four root interfaces and the retained offset checker pass a
separate refresh.

The [latest checkpoint](phase5/README.md),
[fourth checkpoint](phase4/README.md),
[third checkpoint](phase3/README.md),
[second checkpoint](phase2/README.md), and
[first checkpoint](phase1-README.md) retain their respective sources, kernel
records, generator controls, independent reviews and failed attempts. The
[original full-build baseline](../README.md) and attribution are preserved.
Subsequent checks are incremental and keep every reused source/dependency/object
binding explicit. The endpoint is an external proof-assistant theorem; this work
does not supply an internal PA derivation or a minimum-size theorem.
