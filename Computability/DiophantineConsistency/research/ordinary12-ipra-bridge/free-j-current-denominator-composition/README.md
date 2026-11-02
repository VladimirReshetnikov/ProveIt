# Current-provider free-J auxiliary norm with nonzero denominator

`FreeJCurrentDenominator.auxiliary_with_nonzero_denominator` composes the
previous free-J denominator-sign proof and actual graph-to-norm transport in
an arbitrary model of `IΣ₁`. Its hypotheses are precisely the existing ones:
natural ports `p` with `0<p₀`, `p₂<p₀`, `p₃<2p₀` in the model; all twelve
coordinates positive; and an internal zero of the exact 95-operation
free-J literal. These are model hypotheses, not a proof that the compact44
port tuple satisfies them.

Evaluating the actual selected graph expressions in the model's difference
ring, let

```
w = n+z, r = 1-q, h = r w²+q z²-1,
b = 2 r w, A = d h+q r, D = d b, Y = wD-A.
```

The theorem proves the **same** proof-only `D` is nonzero and satisfies

```
D ≠ 0 ∧ q z² D² − (q−1)Y² − D² = 0.
```

Here `q,d,z,n` are the graph expressions selected by
`FreeJOrdinaryTransport.parts`. `denominator_shape` proves by reflexivity
that the denominator-sign packet's `graphD` is exactly the expression
`d·[2(1−q)(n+z)]`; `denominator_eval` transports this expression into the
difference ring. The signed pair's strict inequality yields nonzero via
`internalZero_iff`. The norm then follows from the actual unpolarized graph
residual and the generic cleared identity, which already account for the
polarized graph factor. `D` is a proof expression, not a literal gate or an
extra quantified coordinate.

This is a model-level result. It **does not** prove `D | Y`, integrality of
the reconstructed ordinary witness, the strong norm, compact44 checker
calibration, or the existence of the required proof in iPRA. Those remain
separate obligations; in particular no circular use of the strong norm is
made here.

## Rebuild and evidence

The 70-source project provider was independently audited in
[the coexistence-pair audit](../../../reviews/ordinary12-coexistence-pair-independent-audit/CHECK.json).
The new replay starts from each of its separately built author and peer
outputs, then rebuilds all 12 source-declared suffix modules on each side:
first divisibility, first transport, main orientation, Pell indices, early
window, early index, index comparison, early size, V bound, denominator
sign, signed graph transport, and this composition. No historical project
object is included in these suffix overlays. The replay pins the suffix
sources and audited parent pair, checks every module's exact direct imports,
rejects unexpected axioms, warnings and `sorryAx`, compares corresponding
object hashes and axiom reports, and compares the parent before and after.

The [paired receipt](evidence/receipt.json) records all 24 compiler exits,
commands, source/object hashes, sampled peak RSS, axiom reports and direct
imports. The [terminal observation](evidence/terminal.json) records that
actual wrapper session `52014` exited `0` and printed receipt SHA-256
`a9517710d23a1576f04610ef00f3e16038086eed2956fddc2cd0cf76f006ef7b`.
All 24 compiler and dependency-check exits were `0`; sibling source hashes,
object hashes and axiom reports matched. The final composition object SHA is
`d9ac9454128d5ee18a511962be0ba9446f5e09640c8fc343a59cd95d0522d8f7`;
its final theorem reports `[propext, Classical.choice, Quot.sound]`. The
largest observed per-process RSS sample was `2176471040` bytes. Both sides'
compiler logs are retained under `evidence/author` and `evidence/peer`.

The live driver checked the parent pair and independent audit pins, but
read the 70-source manifest used for its initial closure list without
hash-checking that file at that precise read. The reviewer separately
observed the repository and frozen copies afterward at the audit's hash;
that later observation does not prove what was read at the earlier instant
or exclude transient changes. Exact direct-import checks and the pinned
parent comparison are separate evidence, and this manifest-at-read caveat
remains. The inherited Foundation outer-wrapper exit, dynamic provenance,
and package-transitive dependency ancestry are also not established here.
The [independent suffix audit](../../../reviews/ordinary12-current-denominator-independent-audit/CHECK.json)
exited `0`; it checked both provider and suffix artifact chains, all 24
compiler logs and objects, and reconstructed the direct-import closure at
audit time. It retains the manifest-at-read and inherited ancestry caveats.

The driver samples only the leader's RSS and host free space; the limits are
not hard quotas or total-process-tree accounting. Its reviewed signal handler
signals the verified group and reaps the leader, using Linux subreaper
support. Controls also observed reaping specific same-group descendants;
they do not establish a general descendant-reaping guarantee. This does not
cover deliberately escaped descendants, wrapper SIGKILL, PID reuse or nested
reparenting races, or unobserved resource changes between samples.
[Monitor controls](evidence/monitor-controls.json) include missing
RSS, transient recovery, no-sample fast exit, signal and exception cleanup;
independent review is recorded separately in
[the RSS-retry audit](../../../reviews/ordinary12-rss-retry-independent-audit/README.md).

## Retained failed and exploratory attempts

- `observations/attempt01-*`: wrapper exit `1` on a missing-RSS race; the
  compiler's exit was **not observed**, even though its output is retained.
- `observations/attempt02-*`: wrapper exit `1` after 11 author modules passed;
  the composition compiler failed on cast normalization and a redundant
  rewrite, with `sorryAx` in the failed reports. Its driver revision also
  had an independently demonstrated SIGTERM gap.
- `observations/attempt03-*`: one exploratory author compiler exited `1` on
  natural versus integer numeral casts. `attempt04-*` records a later one
  author compiler exit `0`, not a paired replay.
- `observations/rebuild03-*`: the later corrected wrapper exited `1` after a
  transient missing RSS sample at author denominator exit. The compiler
  itself exited `0`, but the wrapper correctly rejected the incomplete
  measurement. Bounded retry was independently reviewed before the paired
  run above.

For reproduction, use a fresh direct `/tmp/ipra-freej-current-denominator-*`
output path while the exact historical 70-source pair, package and terminal
pins named by the script are available. Coordinate other Lean processes:

```
python3 -I -S replay.py --output /tmp/ipra-freej-current-denominator-new
```
