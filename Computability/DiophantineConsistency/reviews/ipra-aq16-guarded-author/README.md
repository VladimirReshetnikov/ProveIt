# Guarded AQ16 author-only run

The guarded `author-only-extension/run.py` compiled the pinned 52-module
`research/aq16-witness-transport/author-additions.json` in one fresh project
overlay over the audited AQ29 author parent. It rebuilt the complete
44-module AQ22/AQ17 chain and all eight AQ16 additions; it did not combine
separately compiled exploratory overlays. The runner used idle CPU and I/O
priority, one Lean worker, input/output guards and an 8 MiB/s hash throttle.

- Manifest SHA-256:
  `081e343d107f6ff1e73b1bfded119dd3698f363169ae24c25a07b60ddff33a0d`.
- Pinned source commit: `a8a528414339a138adac3d409ebe492c359e8f12`.
- State: `AUTHOR_ONLY_PASS`, 52 module exits zero, 147 recorded direct
  imports, state SHA-256
  `f6b287f2857c050fd2fdfafa4501853cf41bfd5b15bfc2b0d8ff0cf9884514bd`.
- Tool session 10970 returned actual exit 0 and its complete output is saved
  in [`process.log`](process.log); the separate
  [`terminal-observation.json`](terminal-observation.json) records this.
- This packet preserves the exact manifest, runner, state, all copied Lean
  sources and module logs. Binary outputs remain at
  `/tmp/ipra-aq16-complete-guarded-author-20261101/lib` while that directory
  persists.

The runner checked the requested diagnostic names and absence of `sorryAx`
or unexpected Lean metatheory axioms. The transport's general result uses
beta ≥ 2, with the selected historical port proved to satisfy that bound.
The standard endpoint states AQ16 no-zero equivalence to the selected
Foundation consistency sentence under the recorded embedding and
Gödel–Gentzen translation.

This is one historical **author-only** run. Its [independent artifact audit](../ipra-aq16-guarded-author-independent-audit/README.md)
passed; a matched peer replay remains pending. It does not prove formal PDF semantics or
identify the translated consistency formula with untranslated Con(ZFC).
It inherits the parent provider's package-transitive, dynamic-load,
between-observation and unobserved Foundation wrapper-exit limitations.
The guarded observations do not constitute a continuous input trace.
