# Guarded AQ17 author-only run

The guarded `author-only-extension/run.py` compiled the pinned 44-module
`research/aq17-witness-transport/author-additions.json` in one fresh project
overlay over the audited AQ29 author parent. It rebuilt the full 37-module
AQ22 chain and all seven AQ17 additions; no separately compiled exploratory
AQ22 or AQ17 objects were combined. The runner used idle CPU and I/O priority,
one Lean worker, input/output guards and an 8 MiB/s hash throttle.

- Manifest SHA-256:
  `96cd989a4abaf88c0c181e14a72946b3af1b58f4efc485a63ff1687c56918378`.
- Pinned source commit: `1eae3a0a882e8bba1ee0fecc6461dd1f0602d06d`.
- State: `AUTHOR_ONLY_PASS`, 44 module exits zero, 123 recorded direct
  imports, state SHA-256
  `0ac4cf0425d3a405fdd6bdf5450d6a7602fb8a15479f26547ec68f739c09b3f7`.
- Tool session 18775 returned actual exit 0 and its complete output is saved
  in [`process.log`](process.log); the separate
  [`terminal-observation.json`](terminal-observation.json) records this.
- The package preserves the exact manifest, runner, state, all copied Lean
  sources and module logs. Binary outputs remain at
  `/tmp/ipra-aq17-complete-guarded-author-20261101/lib` while that directory
  persists.

The runner checked the requested diagnostic names and absence of `sorryAx`
or unexpected Lean metatheory axioms. The standard endpoint states AQ17
no-zero equivalence to the selected Foundation consistency sentence under
its recorded embedding and Gödel–Gentzen translation.

This is one historical **author-only** run. Its [independent artifact audit](../ipra-aq17-guarded-author-independent-audit/README.md)
passed; a matched peer replay remains pending. It does not prove formal PDF semantics or
identify the translated consistency formula with untranslated Con(ZFC).
It inherits the parent provider's package-transitive, dynamic-load,
between-observation and unobserved Foundation wrapper-exit limitations.
The guarded observations do not constitute a continuous input trace.
