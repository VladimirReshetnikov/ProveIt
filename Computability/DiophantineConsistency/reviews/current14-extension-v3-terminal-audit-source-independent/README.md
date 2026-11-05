# Independent source review of the pending v3 terminal audit

The corrected [terminal audit](../current14-extension-v3-terminal-independent/audit.py) was reviewed read-only at SHA-256 `572f47d8361b58f342bb1b11725e76c1099a1bc67a0d9996cc00443ff5ec5236`. No live audit, supervisor, coordinator or Lean command was run by this review. Its **success path remains untested**; the retained preterminal refusal is not a successful extension or audit.

The audit requires a separately recorded actual supervisor-session exit of 0, a matching supervisor receipt with coordinator-child exit 0, and a pinned client runner. It calls the reviewed client authentication, which reuses the v3 coordinator's terminal verifier and base/provider gates. It then separately checks the 61 recorded sources and objects, dependency logs and their one-or-two-identical-`Init` multiplicity, declared import names, direct producer routes and guards, compilation logs and selected owned-session receipt fields. It checks all output and overlay guards, calls client authentication again, and requires the terminal observation and supervisor receipt hashes to remain stable.

An earlier source-attribution issue was corrected before this review: the audit now captures its own initial source hash and requires that hash and the pinned client runner hash to remain unchanged at the end. These are point-in-time checks and do not rule out transient modifications between observations. The actual supervisor outer-session exit must still be observed separately and recorded; a wait timeout is not an exit.

The [checker](check.py) authenticates the corrected audit, client runner and retained preterminal refusal, and checks the relevant source gates without executing the audit. The refusal records exit 1 for missing observed supervisor terminal evidence. The success path may still fail on actual record shapes or resource conditions and must be preserved and reported as such if it does.

This would be a single artifact cross-check that reuses the reviewed verifier, not a second Lean replay, independent process trace or full package-transitive/dynamic provenance audit. No positive result or completed extension is asserted here.

```
python3 -I -S -B path/to/current14-extension-v3-terminal-audit-source-independent/check.py
```

The deterministic source-review output is frozen in `result.json`.
