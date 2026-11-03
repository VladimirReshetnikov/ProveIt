# Source and outside evidence for a BFS-compatible reverse replay

`plan.py` pins thirteen reverse-stage sources, matching captured source snapshots, successful historical Lean receipts, exact stdout/stderr logs and theorem-specific axiom reports. It validates source-import ordering using the earlier direct-import plan. The source-plan receipt does not inspect the live parent provider or assert that the thirteen stages compile on it.

`capture-outside.py` separately captures `Mathlib.Algebra.Order.Ring.Basic`, the one direct outside import absent from the recorded 80-object BFS outside baseline. Its complete companion presence, targets and hashes are in `observations/outside-attempt01/result.json`. This records one direct outside bundle, not the transitive package or dynamic closure.

A held follow-on runner template is in `../trace75-bfs-compatible-reverse-rebuild/`. It must not be launched before the live 31-stage parent has terminal PASS plus an actual outer exit 0; only then may its final parent and outer receipt hashes be inserted and the resulting runner independently reviewed. The four affected modules retained from the earlier BFS baseline inherit source/object ancestry limits. Neither this plan nor a successful reverse replay alone establishes a joined iPRA endpoint or a formal external-file binding.
