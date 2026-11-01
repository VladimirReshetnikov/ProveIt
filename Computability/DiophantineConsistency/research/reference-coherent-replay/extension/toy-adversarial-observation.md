# Observed adversarial extension toy

The final-source adversarial real-Lean toy ran at `nice -n 19`, idle I/O
priority, with a 180-second limit. Actual session **60878 exited 0**:

```text
PASS: paired real-Lean strict extension; stale/differing/omitted companions, wrong names, seed/fresh hardlinks, drift and unobserved exit rejected
```

The test's SHA-256 was observed after the run as
`b5438ccb878e12185f4965ef3c69aa5d354dfa2f739bb75bed100b0a03a53e9a`.
This toy uses a simulated freezer observation and deletes its temporary
workspace, so internal logs are not retained. It does not authenticate the
real parent or Foundation provider and does not verify AQ29. The separately
observed [end-to-end toy](toy-integration-observation.md) ran the actual
freezer and was independently rerun.
