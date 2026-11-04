# Ordered-ring scalar growth retry draft

The [first author attempt](../trace74-n4-r5-scalar-growth-draft/README.md) failed at strict-multiplication cancellation. This v2 source changes only that proof step: assuming the opposite comparison, multiply its non-strict inequality by the positive factor and contradict the existing strict product inequality. All theorem statements and other proof steps remain unchanged. This source is unchecked, and does not bind any premise to a graph zero.

The [independent repair-source review](../../reviews/trace74-n4-r5-scalar-growth-repair-source-independent/README.md) found the change mathematically valid. The held runner and `prelaunch/` receipt have been prepared for separate launch review and coordination; no Lean check of v2 has been claimed.

The [independent v2 prelaunch review](../../reviews/trace74-n4-r5-scalar-growth-v2-prelaunch-independent/README.md) approved the pinned source and runner for one coordinated check.

One author run completed in actual tool session 75156, exit 0, fully reaped. The [retained terminal](observations/attempt01/terminal.json) SHA-256 is `1d96905eecce9803be78494838568475e7962502c3c2819e5ae7a85f31504668`; the produced object is `/tmp/trace74-n4-r5-growth-v2-di4128zr/lib/Trace74N4R5ScalarGrowth.olean`, SHA-256 `ea78daba5784cedb2f5b8be5e06e6e22094d1a501471caecef0a035af661ad63`. All three printed reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The [independent result audit](../../reviews/trace74-n4-r5-scalar-growth-v2-result-independent/README.md) passed. These are conditional ring estimates; no graph exclusion follows without separately checked bindings and divisibility.
