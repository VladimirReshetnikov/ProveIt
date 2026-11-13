# Exploratory fixed-graph temporal clean target

`TemporalSafeDigit.safe` proves in every IΣ₁ model that, for a bounded word and an in-range target, a zero selected cyclic source and two Boolean cyclic predecessor source digits make the actual bit-rotated target digit zero and its cyclic predecessor at most `Exp.exp 66`. `TemporalSafeCyclic.safe` adapts this to the two-offset predecessor form using a model proof of cyclic nesting.

`FixedGraphTemporalClean.graph_temporal_clean` assumes positive graph coordinates and literal graph zero at the fixed symbolic ports and `paramKernel rho`. It retains the same graph N,w and indexed b=1 `CarryInput`, and selects `t=4393` or `t=5495` such that the actual fractional temporal word has digit zero at t and digit at most `Exp.exp 66` at `cyc (8807*N) t 1`. The q/r split and all cyclic wrap cases are model-level proofs, not an extrapolation from the finite Python calculation.

Author-only compiler sessions 34072, 33901 and 90801 actually exited 0 without warnings or `sorryAx`; their named reports use `propext`, `Classical.choice`, `Quot.sound`. Exact sources, logs, provider paths and direct object hashes are retained. The same fresh author overlay and locally rebuilt dependencies documented in commits 9403a827c7, 778847d293, 86e36b4034, ae249d0592, ffe7765fba, 81417adafb, 076701dc40 and 8295d3bf5e were used. This is exploratory single-side evidence, not a paired replay or independent artifact audit.

The temporal bound alone does not prove a clean carry: the weighted non-temporal predecessor contribution and incoming carry must still be bounded together. The theorem does not establish graph-column/decoder correctness, retained-K or port-byte binding, machine equivalence, or an internal iPRA theorem.
