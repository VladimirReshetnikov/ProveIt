# Two-target sharing with direct aliases

No smaller circuit survived this bounded extension of
`../current14-carrier65-two-target-sharing/`. It additionally permits either
or both rebuilt targets to be a **zero-gate alias** of the shared value; all
downstream references, including the output, are redirected before liveness
is counted. This fills a specific gap in the earlier paired screen. It is not
a global lower bound or a general zero-equivalence search.

The shared value may be one earlier existing node, one newly computed binary
`+`, `-`, or `*` gate on nodes available before the first target, or one new
fixed integer leaf. Each of the two original target values must be preserved;
each replacement is either that shared value directly or a one-gate form
`h+x`, `h-x`, `x-h`, or `h*x` using an earlier node. The rest of the source
graph is retained, with references redirected for eliminated targets.

The checker pins the actual graph, authenticates all four port payloads, and
filters using three deterministic positive-witness samples at each of three
verified primes. It checks that every nonliteral sampled scale is nonzero at
every sample, so no division case is silently skipped. Any fixed integer has
residues at all three primes. An exact identity in this enumerated family
must survive the filters; any survivor would require an exact symbolic proof.

For the current graph it formed 14,300 target requirements and 15,225 possible
shared binary gates, then checked 655 complete paired replacements. None
reduced the 65 live binary gates. Both positive controls pass: the prior
genuine two-target 5→4 sharing example, and a separate duplicate-target
example in which both target rows can be aliases of a shared `x+y` value.
The three deterministic receipts are [result.json](result.json),
[control.json](control.json), and [alias-control.json](alias-control.json).

This does not search more than two targets, more than one shared intermediate,
more than one gate per nonalias target, other simultaneous row changes, or
transformations valid only on graph zeros. It invokes no Lean process and
establishes no global operation bound or new iPRA endpoint.
The independent external review is in
`../../reviews/current14-carrier65-two-target-alias-sharing-independent/`.

From the DiophantineConsistency directory:

```sh
python3 -I -S -B research/current14-carrier65-two-target-alias-sharing/screen.py --control > /tmp/carrier65-alias-control.json
cmp /tmp/carrier65-alias-control.json research/current14-carrier65-two-target-alias-sharing/control.json
python3 -I -S -B research/current14-carrier65-two-target-alias-sharing/screen.py --alias-control > /tmp/carrier65-alias-only.json
cmp /tmp/carrier65-alias-only.json research/current14-carrier65-two-target-alias-sharing/alias-control.json
python3 -I -S -B research/current14-carrier65-two-target-alias-sharing/screen.py > /tmp/carrier65-alias.json
cmp /tmp/carrier65-alias.json research/current14-carrier65-two-target-alias-sharing/result.json
```
