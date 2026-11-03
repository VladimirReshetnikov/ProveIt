# Independent prelaunch review: trace75 BFS all-block word

**GO for one coordinated author check**, with the reviewed runner and outer
wrapper. This is a prelaunch review, not a Lean replay or proof of halting.

The checked client is `research/trace75-bfs-all-block-word-prototype/`:

- source SHA-256 `d2157679d53263ce59e7cf094830f6c8ba577135ebdd2e9c650a3d88e63f7c23`;
- runner SHA-256 `4172a061d494ceae5a4e0684077ea682203f22f359505a95dd3cb54ce7a59081`;
- outer wrapper SHA-256 `49886407d842ba38858d41a92319394441b19bc6728780c63d21b51a158aee08`.

The source adapts the corresponding checked 80-row client. It retains the
four exact symbolic direct-BFS port equalities and positive trace75 zero. It
identifies the two independently selected model lengths through their common
radix, and proposes a represented base-1024 row with a selected tile and
matching copy word at each block. It does not bind external coefficient files
or prove a machine-halt or iPRA endpoint.

`check.py` independently rehashes 34 pinned inputs, all 13 regular client
source/object roots and their matching PASS producer receipts, the 1,977
project objects and 80 outside providers including companion presence, bytes,
and resolved targets. It checks the actual ordered search roots for earlier
shadows and recomputes the captured BFS subtrees: `DirectBFSOrbitRowWord`
has 330 project and 29 outside modules; `ArithmeticPackingBlocks` has 7
project and 4 outside. The captured result is in `result.txt`; these checks
reflect the filesystem at audit time, with historical source/object, package,
dynamic and external-file limitations inherited from the producer records.

In an isolated temporary copy, all 18 actual runner policy-function controls
passed, and the outer wrapper rejected a modified runner before creating an
attempt or launching a child. The reviewed wrapper pins the runner, preflight
and policy receipt; it enforces no-clobber and records the actual child exit.
The runner checks memory and process limits, exact Lean axiom output, direct
serialized imports, stable client roots and provider union. Capture and audit
the terminal result after the coordinated run; do not treat this review as an
author-check result.

`check.py` SHA-256 `3e033398c09beffa2928232ecaee6a8851e6dd0705c1df4b5b326f3a8c487c01`;
`result.txt` SHA-256 `fd291fb523355baf984f2f12c07461c2c37e4ecc085394c5bc97b674ba91580a`.
