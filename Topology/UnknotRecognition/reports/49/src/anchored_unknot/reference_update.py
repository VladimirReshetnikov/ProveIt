"""Verbatim apply_projection function from the inspected ProveIt source.

Repository: VladimirReshetnikov/ProveIt
Commit: 7518823550fbc8c217bc8be0113fe52002e77465
Path: Topology/UnknotRecognition/fast/fastunknot/primitive_projection.py
Whole-file Git blob: 0aff98067b485d285a9c8026fcac56ae9934edc0
License: MIT-0, as stated in that module and the repository.

Only the updater is reproduced; tests use the standalone Arena protocol.
This is not an execution of the complete production package.
"""


def apply_projection(arena, roots, alive, selected):
    """Apply an internally proved disjoint round, retaining original root slots."""
    images = {}
    for evidence in selected:
        arena.tick()
        a,b = evidence['generators'];u,v = evidence['primitive_vector']
        sign = 1 if v>0 else -1
        # Reuse a as a new quotient generator; orient it so a's image is positive.
        for g,power in ((a,abs(v)),(b,-u*sign)):
            images[g] = arena.power(arena.letter(a if power>0 else -a),abs(power))
            images[-g] = arena.power(arena.letter(-a if power>0 else a),abs(power))
    mapped = {0:0}
    # Snapshot traversal before adding concat nodes; images are substituted once.
    for node in arena._reachable(roots):
        arena.tick()
        rule = arena.rules[node]
        mapped[node] = (images.get(rule[1],node) if rule[0]=='t' else
                        arena.concat(mapped[rule[1]],mapped[rule[2]]))
    roots[:] = [mapped[root] for root in roots]
    for evidence in selected:
        arena.tick()
        roots[evidence['relation']] = 0
        alive.remove(evidence['generators'][1])
    arena.stats['projection_rounds'] = arena.stats.get('projection_rounds',0)+1
    arena.stats['projection_pairs'] = arena.stats.get('projection_pairs',0)+len(selected)


def native_witnesses(batch):
    return [dict(generators=[w.a, w.b], primitive_vector=[w.u, w.v], relation=w.slot) for w in batch]


def exact_rle(arena, roots, cap=100000):
    """Exact run-length expansion; suitable only when the run count is small."""
    vals = {0: ()}
    for node in arena._reachable(roots):
        rule = arena.rules[node]
        if rule[0] == 't':
            vals[node] = ((rule[1], 1),)
            continue
        left, right = vals[rule[1]], vals[rule[2]]
        if left and right and left[-1][0] == right[0][0]:
            merged = left[:-1] + ((left[-1][0], left[-1][1] + right[0][1]),) + right[1:]
        else:
            merged = left + right
        if len(merged) > cap:
            raise ValueError("RLE audit cap, not a recognition failure")
        vals[node] = merged
    return [vals[root] for root in roots]
