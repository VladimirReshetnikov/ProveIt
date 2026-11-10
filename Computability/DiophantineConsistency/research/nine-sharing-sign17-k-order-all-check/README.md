# All K local order blocks and boundaries

This source-only 17-stage client reuses the independently audited, successful
single-context Fin942 weight provider. It proposes the Start/non-Start order
probe, all 15 remaining within-block index/weight checks, and all 15 numeric
and actual-weight interblock comparisons. The runner pins the successful
provider state, outer receipt and audit, checks its 40 source/object/log and
direct-guard records and overlay links, and routes the proposed direct
imports to those exact provider objects. It does not claim a complete
transitive provider trace. It also checks the pinned external witness's
nonzero/order facts and checks all block sources against the audited sample
template; these external checks are not Lean theorems.

Even if the 17 stages succeed, their local facts must still be assembled into
the global hypotheses of the actual physical-rank criterion. Actual candidate
ranks, K coefficient aggregation and external file binding remain separate.
Each Lean child retains the existing 120-second, 4-GiB sampled-RSS and 10-GiB
available-memory limits. The full sequential run could occupy the slot for
several minutes. Author no-Lean preflight exited 0 after correcting a copied
generator hash typo: the first preflight stopped at that pin before creating
any output or invoking Lean.

Runner SHA-256:
`9af30abd986636472a6b76d4ca4786485ba232352f59fadf9686a4ed271e7c03`;
manifest SHA-256:
`00989ec839e9edac1a03867d3ff9a9c002620c0c2a91931b376a5230d09e81ae`.
Each source has its own manifest hash. Independent prelaunch review and an
assigned Lean slot are required.

The initially passing [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-order-all-prelaunch-independent/README.md) was withdrawn after identifying that the runner did not explicitly assert the first-candidate `Init` route against the captured provider, and did not set `LEAN_NUM_THREADS=1`. No Lean run was started from this packet. The [fresh corrected runner](../nine-sharing-sign17-k-order-all-retry-check/README.md) passed its independent terminal audit; this withdrawn packet is frozen.
