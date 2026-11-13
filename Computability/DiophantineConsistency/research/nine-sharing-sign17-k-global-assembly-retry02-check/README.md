# Global K candidate-rank assembly: chunk00 unfolding retry

This checked five-stage retry retains the prior audited failure's
statements, all other 28 chunk branches and provider/resource guards. Its
only source changes add `Fin.castLE` unfolding in the two chunk00
simplifier sets, addressing the remaining variable-cast mismatch. The runner
pins both failed attempts and their audits and enforces the exact source
deltas. The checked candidate-rank theorem leaves K coefficient aggregation
and external file binding separate. Author no-Lean preflight
exited 0.

Runner SHA-256:
`32ff381103a10e321922b2860e997afbd67d052dff4b39d83bc980677a7dc534`;
manifest SHA-256:
`db11f0517267e4fbde5446e5532e7021634c78aa33586c9b45e0814cbe5025df`;
source SHA-256:
`c1cd2d590d332acbfa59e88356a49c597d27ab6e4cea17545b522e94ac6f4ab4`.
The run used the established independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-global-assembly-retry02-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-global-assembly-retry02-terminal-independent/README.md) passed; the packet is frozen.
