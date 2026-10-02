# Fixed-arity amplitude: independent analytic verdict

Date: 2026-10-02.

**Approved:** the reviewed proof establishes a finite strictly positive relaxed k-ary tree amplitude for every fixed k≥3, with relative error O_k(n^−1/6). No fatal gap remains in the moving-boundary compactness argument, form liminf/min–max, phase norms, forward/adjoint residuals, compressed singular gap, tracking, endpoint extraction, or positivity.

Reviewed proof SHA-256: `9be0c0aaf02b6918a8015c6d059664851d393e9ea8e75ac4a31e082c34434ee2`.

Detailed audit: `analytic-audit.md`, SHA-256 `974c250275efc483acec31d9ea3806ba91a670d70cb70071ae757eaa1f45cbe9`.

The approval includes the detailed analytic justifications in that audit. Recommended additions to a standalone presentation are explicit initialization d_(0,0)=1, localization before the terminal-edge identity, row-loss convergence from strong L², the Hardy/form-domain step, and the singular-overlap compression inequality. These are exposition clarifications, not unresolved hypotheses.

The published positive lower Theta bound is used only after existence of the normalized limit is established; the source recurrence and normalization were independently verified. The exact script was independently rerun: 2,095 rational checks pass. Those checks are not the analytic proof.

No uniform-in-k, all-orders, DFA, compacted-tree, or numerical amplitude-evaluation claim is included.
