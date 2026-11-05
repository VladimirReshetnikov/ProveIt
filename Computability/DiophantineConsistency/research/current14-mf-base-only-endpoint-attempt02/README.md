# Matrix-free printed-port endpoint, attempt 02

Status: **source draft, not Lean-checked**. This packet preserves attempt 01 and uses a fresh isolated output directory. The sole Lean-source change unfolds the two definitions of the same finite geometric sum in `omega_eq` immediately before `ring`. Both unchanged definitions and the attempted rewrite are visible in the source; success is not assumed.

The first attempt and its failed Lean log are preserved separately at `research/current14-mf-base-only-endpoint-attempt01-result/`; the original base-only draft and its reviewed runner controls remain at `research/current14-mf-base-only-endpoint/`. The first compiler log showed only the geometric-sum `omega_eq` error; it did not complete the endpoint client.

The runner is derived from the independently reviewed base-only runner, with only the updated source digest and a new output path. It authenticates the fresh base and Foundation provider, checks isolated direct inputs and output inventories, and retains logs and actual child-process receipts. The prior 61-module extension is not used. The source states an outer Lean existential over four integer ports and an iPRA derivability statement; it does not parse TeX/PDF or by itself prove ZFC consistency.

A fresh pure preflight and independent review must precede any coordinated Lean attempt.
