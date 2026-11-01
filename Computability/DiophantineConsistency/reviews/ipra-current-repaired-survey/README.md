# Current-source survey over the repaired 73-module provider

This is a frozen **build survey**, not a Lean proof. It starts at
`IPRAAdaptiveNativeZFCChecks` and records 1,099 project sources, their imports,
and a conservative 258-module rebuild order over the independently compared
73-module repaired peer at `/tmp/ipra-frozen-ancestry-repair-6ftdeyrq`.
The capture observed no source drift during the snapshot. The selected
provider's earlier fixed-snapshot repair and original project-origin audits
are inputs, not independently repeated proofs of its entire ancestry.

The eleven initial source seeds are ten sources changed from the repaired
frozen parent and the new `ZFCinPA.NativeZFReplacement`. The affected closure
uses both current imports and the recorded original project environments of
selected objects. The survey checks selected object hashes and repairs' direct
imports; unavailable or untraced origins are treated as rebuild seeds. The
106 external modules and all present and absent direct object/companion paths
are captured; comparison with the repair plan's direct paths found no newly
present companion files. Dynamic and transitive external ancestry is not
independently recompiled here.

`survey.py` generated `manifest.json` and `sources/` from the live workspace.
`check_lean_deps.py` separately ran Lean's `--deps` parser on every frozen
source: all 1,099 explicit import sets matched (`lean-deps-receipt.json`).
`check_closure.py` independently recomputed the fixed point and checked the
captured sources, selected project objects, recorded source origins, repaired
direct externals, and external companion presences and absences; it reported
`PASS 1099 sources 258 rebuild` (`closure-receipt.json`). The closure checker
also observed no workspace source drift at its run. Neither script compiles
the 258 modules; author and independent replay, full output comparison, and
source-current checks are still required. The original 848-module ancestor
remains author-only, and package-transitive/dynamic ancestry remains inherited.

The snapshot records its original `observed_head`; later commits confined to
evidence or research files need not alter this source graph. A build may be
called source-current only after rechecking all reachable sources and the
graph at its own start and end. Do not edit the frozen sources in this packet.
