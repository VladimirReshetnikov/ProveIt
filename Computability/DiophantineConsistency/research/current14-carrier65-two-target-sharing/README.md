# Coordinated two-target sharing screen

No smaller circuit survived this bounded, current-port screen. It searches a
different family from the prior single-target screens: introduce one shared
intermediate, then rebuild **two** existing target rows around it. This is a
negative result only for the precise families below, not a global lower bound
or a search of arbitrary zero-preserving transformations.

For each target, infer a common value `h` from one-gate forms
`h+x`, `h-x`, `x-h`, or `h*x`, where `x` is an earlier source node or one
of the fixed leaves 0–4. The same `h` must serve two distinct targets. It may
be an earlier existing node, one newly computed binary `+`, `-`, or `*`
gate on nodes available before the first target, or one new fixed integer
leaf. Rebuild both rows, retain the rest of the graph, and count live binary
gates from the output. The later target may use the first target, whose value
is required to remain unchanged. Each target still costs one gate; deleting
a target by direct alias is outside this screen.

The actual four fixed ports are checked against compressed and raw hashes.
Three deterministic positive-witness samples are evaluated modulo each of
three verified primes. Every sampled nonzero source node is invertible in its
prime, so the four inferred forms introduce no unresolved zero divisor. Any
fixed integer leaf has residues at all three primes. An exact identity in
the enumerated family must survive these samples; a survivor would still need
an exact symbolic proof.

The screen formed 14,235 target requirements and 15,225 potential shared
binary gates, then tested 560 complete paired replacements across 340
signature/target-pair combinations; none reduced the 65 live gates. A positive control genuinely requiring
joint sharing is detected:

```
a=x+y; b=x-y; c=a+z; d=b+z; out=c*d       # five gates
h=x+z;          c=h+y; d=h-y; out=c*d       # four gates
```

Replacing either target alone does not remove enough gates, while the paired
rewrite removes `a,b` and adds `h`. The detected control and current result
are stored separately as [control.json](control.json) and
[result.json](result.json).

The screen does not include direct target alias elimination, more than one
fresh intermediate, more than two target rewrites, more than one gate per
rebuilt target, changing other rows, or transformations valid only on zeros.
It does not invoke Lean or establish any global operation bound.
The independent external review is in
`../../reviews/current14-carrier65-two-target-sharing-independent/`.

From the DiophantineConsistency directory:

```sh
python3 -I -S -B research/current14-carrier65-two-target-sharing/screen.py --control > /tmp/carrier65-joint-control.json
cmp /tmp/carrier65-joint-control.json research/current14-carrier65-two-target-sharing/control.json
python3 -I -S -B research/current14-carrier65-two-target-sharing/screen.py > /tmp/carrier65-joint.json
cmp /tmp/carrier65-joint.json research/current14-carrier65-two-target-sharing/result.json
```
