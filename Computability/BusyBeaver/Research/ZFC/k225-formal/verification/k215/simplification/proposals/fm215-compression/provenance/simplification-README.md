# Shorter checked K215 proofs

The literal 215-state machine and its halting and nonhalting endpoint statements
are unchanged. The [latest Lean check](phase3/README.md) validates the 185-module
primary closure and both typed endpoint clients, using the pinned original
full-build objects for unchanged modules. All ten endpoint reports use only
`propext`, `Classical.choice`, and `Quot.sound`; both audits have zero warnings.

| Proof source | Original | Current |
| --- | ---: | ---: |
| Lean dominated implication | 689,857 bytes | 35,185 bytes |
| Lean AX routine | 202,222 bytes | 7,563 bytes |
| Lean source data | 653,569 bytes | 456,548 bytes |
| Lean site-coverage facade | 107,243 bytes | 14,916 bytes |
| Lean register determinism | 17,209 bytes | 12,988 bytes |
| Rocq dominated implication | 921,691 bytes | 22,673 bytes |

The main changes share mathematical arguments instead of repeating their
instances. Offset-bisimulation symmetry eliminates sixteen reverse-certificate
modules; guarded implication lemmas avoid expanded substitutions; one general
enumerator theorem covers both starts; and the AX routine composes a finite
word of existing macro contracts. The import closure shrinks from 204 to 185
project modules. The four root interfaces also pass a separate refresh.

The [latest checkpoint](phase3/README.md),
[second checkpoint](phase2/README.md), and
[first checkpoint](phase1-README.md) retain their respective sources, kernel
records, generator controls, independent reviews and failed attempts. The
[original full-build baseline](../README.md) and attribution are preserved.
Subsequent checks are incremental and keep every reused source/dependency/object
binding explicit. The endpoint is an external proof-assistant theorem; this work
does not supply an internal PA derivation or a minimum-size theorem.
