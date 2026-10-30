# Exact no-zero source closure

The 26 local imports of `FoundationHACurrentNoZero2011` were rebuilt from frozen source snapshots. The author build `/tmp/pra-current-nozero-closure-author-u21ev5n6` and the corrected independent build `/tmp/pra-current-nozero-closure-peer-resume-llv_5qtb` passed final source, snapshot and object authentication. The latter uses independently rebuilt prerequisites over the accepted 60-module provider `/tmp/pra-isigma-final-merge-independent-2tnjbnht/lib`. It retains the original 13 exact-matching independent objects, the independently recompiled KZip object, and freshly rebuilt remaining objects. Root’s fresh same-path independent replay also passed at `/tmp/pra-current-nozero-closure-samepath-independent-vpvwoq8y`; its full logs, independent snapshot copies, and terminal state are retained in `root-independent`. The `author`, `initial-peer-failure`, and `peer-resumed` receipts retain full logs, source snapshots and terminal states where available.

An initial replay failed because KZip's pre-existing unused-simp warning embeds the absolute source path in its object metadata. Both original objects and logs are preserved at the paths and hashes in `kzip-audit.json`. A separate KZip compilation with the independently rebuilt prerequisites and authenticated author snapshot path matched the author object and full log exactly. The corrected replay uses that same authenticated snapshot path throughout and checks an independent source copy and live sources before and after. The warning remains recorded; no source was edited.

Manifest SHA-256: `1e5891f2e38a058569483c7f1fb42cd9b9746a864bd4f10075a195b56f3d5a02`. Foundation, Mathlib and the historical PAHF transitive graph are inherited; `PAHF.PACore` itself is hash-checked. This is the no-zero source closure only, not the ZFC consistency proof predicate or its representation.

```sh
python Computability/DiophantineConsistency/reviews/pra-current-nozero-closure-author-replay/replay-samepath.py --parent /tmp/pra-isigma-final-merge-independent-2tnjbnht/lib --ha-parent /tmp/hacurrent-client-audit-20261029/lib --snapshot-root /tmp/pra-current-nozero-closure-author-u21ev5n6/src
```
