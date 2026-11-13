# Independent review: 80-row main norm, rank, and growth

The reviewed source chain establishes the main Pell norm and a rank-to-main-index *congruence* for a positive zero of the exact Lean 80-row graph in any IΣ₁ model, assuming the first port is positive. The further rank equality and growth claims retain explicit hypotheses. This is not an unconditional graph-to-machine theorem or an iPRA endpoint.

`graph_main_norm` takes the odd ordinate recovered by the earlier noncircular fold and applies the generic Pell recurrence norm. Its main norm is a conclusion. The signed-rank lemma permits both signs; the generic signed rank/index theorem assumes a strong norm, a strong ordinate divisible by `c`, an auxiliary coordinate equation, and the signed square equation. The graph rank/index binding derives these from one shared tuple of graph-zero witnesses.

The general `rank_to_main_index` assumes `c=ycoord r`, `r≥3`, `c²∣ycoord n`, and two signed congruences sharing an auxiliary index. Its local name `hmain` denotes one of these congruences, not a premise that the graph's main norm holds. It obtains the needed divisibilities and reduces the congruence. `graph_rank_main_congruence` takes a recovered `r` and independently extracts a strong/auxiliary tuple; the connecting fact is the same actual graph value `c`. Its two congruences and strong ordinate refer to the same latter tuple. Source review found no `half_index` invocation in the six main/reduction/rank/equality/growth/index sources checked here; full transitive source ancestry was not audited here.

`graph_rank_equality_of_small` explicitly assumes that **every** signed-pair representation of the actual graph rank has `2*absdiff rp rn<c`. It derives rank positivity and then `absdiff rp rn=r`. The size premise is not established by this packet, nor is rank's sign fixed.

The corrected `power_bound_scaled_minus` uses the actual truncated parameter `S*(X+1)-1`. Its hypotheses include `X≥16`, `S≥1`, `r≥2`, the stated remainder equations, and two Pell-coordinate equations at the *aligned* indices `2r+1` and `r+1`. `first_index_ge_two` derives `2≤n` for a graph zero only after assuming the representation of the first index in `hcoord`; it does not show alignment. `graph_growth_of_alignment` assumes `X≥16` and, universally for its displayed admissible first and main indices, `3≤n` and `m+1=2n`. Neither theorem proves those alignment and size premises. There is no circular use of an unproved size or alignment bound in their displayed statements: those needed bounds remain explicit assumptions.

## Receipt finding

Five successful scaled-growth receipts pin the hash of `run.py` rather than the executing variant. Their corresponding variant/receipt pairs are:

* `run-graph.py` / `observations/attempt01/terminal.json`;
* `run-cabovex.py` / `observations/cabovex-attempt01/terminal.json`;
* `run-graphindex.py` / `observations/graphindex-attempt01/terminal.json`;
* `run-kpos.py` / `observations/kpos-attempt01/terminal.json`;
* `run-size.py` / `observations/size-attempt02/terminal.json` (its failed `size-attempt01` is similarly affected).

Thus those receipts cannot authenticate the actual executing runner. This is a provenance defect; the graph-growth and graph-index source snapshots, compiler output logs, objects, and currently selected direct input hashes were separately checked against their recorded values, and no Lean theorem failure follows. The corrected abstract growth and index-one staged runners use `sha(__file__)`; their current runner hashes match their records. Fresh corrected guarded runs are being prepared separately.

The five affected checks were subsequently repeated with self-pinning runners.
Their unchanged sources and bit-identical objects, and the corrected
graph-index → c>X → Kpos provider chain, passed a separate
[independent receipt audit](../ten-positive-80-corrected-receipts-independent/README.md).
That audit did not replay Lean or reconstruct all inherited ancestry.

`check.py` checks the accepted receipts and direct import selections shown in its captured output, recorded source and object hashes, selected predecessor hashes, reported axioms and sampled resources. For the two affected graph variants it deliberately checks the historically recorded `run.py` hash and does **not** claim it authenticates the actual variant. It does not independently audit the other three affected packets' objects here. Prior providers, package/dynamic inputs and historical source-to-object links are not fully inventoried. Printed `propext`, `Classical.choice`, and `Quot.sound` are Lean metatheory dependencies, not iPRA object axioms. No Lean replay, graph/PDF binding, or full ancestry reconstruction was performed. The read-only check passed in `observations/attempt01/`.
