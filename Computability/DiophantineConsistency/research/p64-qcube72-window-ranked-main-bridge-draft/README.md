# Window to main index

`FreeMainWindowRankedMain.main_at_rank` identifies the main Pell coordinates
at the actual graph rank `R`, for any IΣ₁ model, natural ports, and actual
positive zero of the 72 graph satisfying `q≥33`, `p₂<p₀`, and `p₃<2p₀`.
The proof composes the checked actual-rank window, generic rank-half bound,
and conditional actual-rank main Pell theorem. Positive coordinates supply
`q≤X` and `q³≤Y`; the window and Pell norm supply `2R<c`.

Attempt02 passed with Lean exit 0, the expected axiom report
`[propext, Classical.choice, Quot.sound]`, no warnings or `sorryAx`, and
stable direct input guards. The source's historical “Unchecked draft” header
predates this check and does not describe its status. This result does not
prove the compact-port specialization, a reverse witness map, an existence
equivalence, or an iPRA endpoint. The separate compact specialization has
encountered memory stops.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainWindowRankedMain.lean` | `3afeff3cacbb6180ae1040d2daff8dce7aad5da9394f7793e0f8cc4260195d50` |
| `check02.py` | `8937be88a55685d5d0daabbc2910291e509cfa95554fa60b24457db4cee4ac98` |
| `observations/attempt02/compile.log` | `63c69af174a16cdb1607bb0ad986fdb203647fd1bb956d9d3e8cf11db30f720a` |
| `observations/attempt02/result.json` | `e033c36e8ad94966f9a22abe2f442f13bf3627495d15b16740b13df271ffbc8a` |
| `/tmp/p64-qcube72-window-ranked-main-priority-check02/FreeMainWindowRankedMain.olean` | `3597c62070070a2cc761b9c5a182de486f7ae04a71f139aadc45cad09513db15` |

The runner guards the source, Lean executable, and direct `actual_window`,
`rank_half`, and `main_at_rank` provider objects. The check used a 2,400 MiB
Lean limit, 120-second timeout, sampled process-group RSS limit of 3.5 GiB,
minimum 10 GiB host available memory, and low CPU and I/O priority. It inherits
the providers' transitive and dynamic ancestry and samples resource use; this
is not a source-only rebuild.

Attempt01 failed on a local cast-shape goal because `YY` had not been unfolded;
its report contains `sorryAx` and it produced no object. Its exact source,
runner, log and receipt are retained in `observations/attempt01/`. The
successful source adds the required local unfolding.
