# Guarded author run for both thirteen-variable standard-iPRA endpoints

The guarded `author-only-extension/run.py` compiled the pinned eight-module
`research/ipra-standard-13-frontier/author-additions.json` in one fresh
project overlay over the independently audited historical AQ29 author
parent. It rebuilt the four standard-theory modules, the 87-gate literal and
native client, and both new standard clients. The 86-gate native statement is
derived from the parent bridge; no separately compiled exploratory extension
objects were combined. The runner used idle CPU and I/O priority, one Lean
worker, input/output guards and an 8 MiB/s hash limit.

- Manifest SHA-256:
  `2a4749c34750dbff650e19b5e5fc7effd98a64774c4051852f3db39221b2f134`.
- Pinned source commit: `72bb86f99414925806059a74f0bf77be7d1c5fc5`.
- State: `AUTHOR_ONLY_PASS`, eight module exits zero, 27 recorded direct
  imports and 13 exact diagnostic occurrences; state SHA-256
  `b6d867bb44502dd78f3b833ebe2c4c23b1a5875a4f065e538abbe9fd0fedfae4`.
- Tool session 3315 returned actual exit 0 and its complete output is in
  [`process.log`](process.log); [`terminal-observation.json`](terminal-observation.json)
  records that observation separately.
- The exact manifest, runner, copied Lean sources, logs and full state are
  retained here. Binary outputs remain at
  `/tmp/ipra-standard-13-frontier-guarded-author-20261101/lib` while it persists.

The runner checked the eight requested square-sum native/standard diagnostics
and five product bridge/native/standard diagnostics for exact names and
absence of `sorryAx` or unexpected Lean metatheory axioms. The standard
clients state equivalences with the selected mapped native refutation and
with the Foundation consistency sentence under the recorded embedding and
Gödel–Gentzen translation.

This is one historical **author-only extension**. Its [independent artifact audit](../ipra-standard-13-frontier-guarded-author-independent-audit/README.md)
passed. A later [historical pair](../ipra-frontier13-historical-pair-terminal/README.md)
matched all eight additions and passed an [independent complete-result audit](../ipra-frontier13-historical-pair-independent-audit/README.md). The separately checked finite
[PDF binding](../frontier13-pdf-historical-lean-binding/README.md) does not
formalize TeX; its fixed decoder/rank recipe remains manually transcribed.
This result is not a current-source claim or an identification of translated
consistency with untranslated Con(ZFC). The parent provider's
package-transitive, dynamic-load, between-observation and unobserved
Foundation wrapper-exit limitations remain.
