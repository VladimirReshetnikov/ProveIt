# Guarded direct-square fourteen-variable standard-iPRA author run

The guarded `author-only-extension/run.py` compiled the pinned five-module
`research/ipra-standard-direct14/author-additions.json` in one fresh project
overlay over the independently audited historical AQ29 author parent. It
rebuilt all four standard-theory additions and the new direct-square client;
it did not reuse exploratory extension objects. The runner used idle CPU and
I/O priority, one Lean worker, input/output guards and an 8 MiB/s hash limit.

- Manifest SHA-256:
  `d2ff86b187c8b4aeb97dc701bfc7ba33b050b38c873cc5ceb6fb174991744690`.
- Pinned source commit: `777716daef4825d6b3023446b457f12d83aca67f`.
- State: `AUTHOR_ONLY_PASS`, five module exits zero, 16 recorded direct
  imports, eight exact diagnostic occurrences, state SHA-256
  `37092f477544b888ba861fb2e4eb7093d0fa592ef0fa0185f724d3127656d0bd`.
- Tool session 50269 returned actual exit 0 and its complete output is in
  [`process.log`](process.log); [`terminal-observation.json`](terminal-observation.json)
  records the observation separately.
- The exact manifest, runner, copied Lean sources, module logs and full state
  are retained here. Binary outputs remain at
  `/tmp/ipra-standard-direct14-guarded-author-20261101/lib` while it persists.

The client asks Lean to report five already compiled direct-square native
theorems and three standard-theory endpoint theorems. The runner checked the
exact names and absence of `sorryAx` and unexpected Lean metatheory axioms.
The two endpoint statements respectively use the selected mapped native
refutation predicate and the Foundation consistency sentence under its
recorded embedding and Gödel–Gentzen translation.

This is one historical **author-only extension**. Its [independent artifact audit](../ipra-standard-direct14-guarded-author-independent-audit/README.md)
passed; a matched extension replay remains pending. The underlying direct-square
literal and native endpoint were compiled in both audited AQ29 parent
siblings, but their separate diagnostic-check module was absent from that
parent snapshot; the five native reports here are newly observed in this
extension. The declared native closure survey recorded 15 workspace drifts.
The result is not a current-source claim, formal PDF semantics, or an
identification of translated consistency with untranslated Con(ZFC). It
inherits the parent provider's package-transitive, dynamic-load,
between-observation and unobserved Foundation wrapper-exit limitations.
