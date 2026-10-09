"""One-sided explicit-layer baseline for separated left and right caps.

Unlike the powered solver this answers a fixed left-cap query and uses only
b live intervals, not 2b. It is deliberately the stronger sequential control.
"""
from compressed_search import Candidate, reduce_family
from disk_algebra import DSU, canonical, disk_cap


def extend(p, q, b):
    np, nq = max(p)+1, max(q)+1
    dsu = DSU(np+nq)
    for i in range(b):
        if not dsu.join(p[i], np+q[i]):
            return None
    outer = [dsu.root(np+x) for x in q[b:]]
    if set(outer) != {dsu.root(i) for i in range(np+nq)}:
        return None
    return canonical(outer)


def run(width, options, repetitions, left_cap, right_cap, allowed_charges=None, *, exact=False):
    allowed = None if allowed_charges is None else set(allowed_charges)
    table = [Candidate(tuple(left_cap), 0, 0, ())]
    pairs = 0; peak = 1
    for _ in range(repetitions):
        generated = []
        for x in table:
            for op in options:
                pairs += 1
                out = extend(x.partition, tuple(op['partition']), width)
                if out is not None:
                    generated.append(Candidate(out, x.cost+int(op.get('cost',0)),
                                               x.charge ^ int(op.get('charge',0)), ()))
        table = [generated[i] for i in reduce_family(generated, exact=exact)]
        peak = max(peak, len(table))
    feasible = [x.cost for x in table if (allowed is None or x.charge in allowed)
                and disk_cap(x.partition, tuple(right_cap))]
    return (min(feasible) if feasible else None), {'composition_pairs': pairs, 'peak_table': peak}
