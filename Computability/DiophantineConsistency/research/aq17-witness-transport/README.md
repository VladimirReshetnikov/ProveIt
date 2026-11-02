# AQ17 historical-overlay witness-transport drafts

These Lean drafts extend the historical AQ22 development to the 17-variable
candidate in `../aq22-positive-binding-survey/`. The literal follows the
99-row pinned graph; `check_literal.py` verifies its 17 variable indices,
four ports, every operation and output, with four mutation controls. The
zero decomposition has eight residuals. The project/extend maps eliminate
the five positive coordinates `scaleVariable`, `mainScaleVariable`,
`ellVariable`, `cSquareVariable` and `deltaVariable`. The transport proves
both directions over the specified arithmetic models, and the model theorem
uses positivity of port 0 to compare positive-shift no-zero statements.

Seven modules compiled successively in one **exploratory**, historical AQ22
author overlay, including the native and standard iPRA clients. The standard
client relates the no-zero sentence to the selected embedded
Gödel–Gentzen-translated Foundation ZFC consistency sentence. Axiom reports
for the selected transport, model and endpoint theorems contained only Lean
metatheory's `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx`. These are not object-theory axioms.

The [observations](exploratory/observations.json) record actual tool exit
codes, source/object hashes, two failed attempts, and the provider paths.
The first literal attempt failed because an empty first Lean search path
shadowed the parent namespace; a fresh tree with file symlinks into the
historical AQ22 overlay resolved this. The first model attempt failed on an
unavailable imported positivity theorem; the successful version reproduces
the historical elementary argument. The [transport log](exploratory/transport.log)
contains two unused simp-argument warnings; no errors occurred.

The development overlay is `/tmp/aq17-develop/lib`, populated with
file-by-file symlinks to `/tmp/ipra-aq22-full-guarded-author/lib`, with new
AQ17 outputs stored as regular files. The latter overlay came from the
guarded AQ22 author run over the AQ29 author parent; the recorded parent
states are pinned in the observations. `LEAN_PATH` paired this development
overlay with `/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib`. These
exploratory compiles did **not** guard every input before and after execution,
and do not constitute a single-overlay guarded replay of the complete AQ22
and AQ17 chain, a peer replay, or a current-source result. They inherit the
parent's package-transitive, dynamic-load, between-observation and
Foundation-wrapper-exit limitations. The `equation17.pdf` display-to-Lean
connection and its fixed decoder/rank transcription boundary are separate
audit questions.

`generate.py` generates only the literal and zero decomposition using pinned
candidate and AQ22 template hashes. Run it and `check_literal.py` in normal
Python; both rely on assertions and reject optimized mode. The other Lean
files are development sources, not part of the regular Lean package.

`build_manifest.py` freezes the prior 37 AQ22-chain additions and all seven
AQ17 additions to Git commit `1eae3a0a882e8bba1ee0fecc6461dd1f0602d06d`,
including exact declared imports and diagnostic names. It produces
`author-additions.json`, whose SHA-256 is
`96cd989a4abaf88c0c181e14a72946b3af1b58f4efc485a63ff1687c56918378`.
The guarded runner's source policy accepted all 44 rows. The subsequent
[single-overlay author run](../../reviews/ipra-aq17-guarded-author/README.md)
exited 0 and passed an [independent artifact audit](../../reviews/ipra-aq17-guarded-author-independent-audit/README.md).
It remains a historical author-only result; a matched peer replay is pending.
