# Latest-merge full project graph audit

Audit-only `/tmp/ha87-full-transitive-n5uzrzgf` returned `AUDIT_PASS` with 727 declared project modules, 93 direct external objects and 279 companions. No Lean proof module was compiled. The subsequent all-source hash postcheck passed; `postcheck.log` lists the seven changed source hashes relative to `../ha87-transitive-postmerge-audit/` and confirms unchanged import edges. The audit is a point-in-time graph check, not an independent proof replay or package-transitive provenance audit.

The focused 87 build `/tmp/ha87-focused-validator-rebase-5zvm8dzr` later stopped for source drift; its terminal state is in `../ha87-residue-import-refresh/`. The invalidated transitive-guard full build also stopped after its child exited; its terminal state is in `../ha87-transitive-first-drift-stop/`. Subsequent full rebases qualify the reconstructed historical transitive environment.
