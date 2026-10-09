"""Normalization-free disjoint primitive-pair rounds, from report 45 (MIT-0).

These internal operations require source-established torsion-freeness for
proper-power donors. They are not verdict APIs for arbitrary presentations.
The source-bound checker reconstructs and replays each complete round.
"""
from .primitive_power import primitive_power_terminal


def projection_metadata(arena, roots, cache=None):
    """Build immutable capped support/count summaries once per allocated node."""
    arena.stats['projection_attempts'] = arena.stats.get('projection_attempts',0)+1
    if cache is None:cache = {}
    meta = cache.setdefault('counts',{0:{}})
    powers = cache.setdefault('powers',{})
    # Stop at cached nodes: across the entire search, each allocated node's
    # capped support/count summary is constructed at most once.
    for root in roots:
        pending = [(root,False)]
        while pending:
            arena.tick()
            node,ready = pending.pop()
            if node in meta:continue
            rule = arena.rules[node]
            if rule[0] == 't':
                x = rule[1]
                meta[node] = {abs(x):(int(x>0),int(x<0))}
            elif not ready:
                pending.extend(((node,True),(rule[2],False),(rule[1],False)))
                continue
            else:
                left,right = meta[rule[1]],meta[rule[2]]
                if left is None or right is None or len(left.keys() | right.keys())>2:
                    meta[node] = None
                else:
                    counts = dict(left)
                    for g,(p,n) in right.items():
                        a,b = counts.get(g,(0,0));counts[g] = a+p,b+n
                    meta[node] = counts
            arena.stats['projection_metadata_nodes'] = arena.stats.get('projection_metadata_nodes',0)+1
    return meta, powers


def plan_projection(arena, roots, alive, cache=None):
    """Greedily select disjoint coherent donors; cache immutable node summaries."""
    meta,powers = projection_metadata(arena,roots,cache)
    selected,used = [],set()
    for slot,root in enumerate(roots):
        arena.tick()
        counts = meta[root]
        if counts is None or len(counts)!=2 or any(p and n for p,n in counts.values()):
            continue
        pair = sorted(counts)
        if not set(pair)<=alive or used.intersection(pair):
            continue
        if arena.lengths[root]==2:
            # Two distinct signed letters are an immediate primitive word.
            vector = [counts[g][0]-counts[g][1] for g in pair]
            evidence = dict(kind='rank_two_primitive_power',relation=slot,generators=pair,
                            primitive_vector=vector,exponent=1,width=1)
        else:
            if root not in powers:
                powers[root] = primitive_power_terminal(arena,[root],set(pair))
            if powers[root] is None:continue
            evidence = dict(powers[root],relation=slot)
        selected.append(evidence);used.update(pair)
    return selected


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


def rank_one_zero(arena, roots, alive):
    """Exact exponent endpoint on raw one-generator circuits; no normalization."""
    if len(alive)!=1:return False
    generator = next(iter(alive));totals = {0:0}
    for node in arena._reachable(roots):
        arena.tick()
        rule = arena.rules[node]
        if rule[0]=='t':
            if abs(rule[1])!=generator:return False
            totals[node] = 1 if rule[1]>0 else -1
        else:totals[node] = totals[rule[1]]+totals[rule[2]]
    for root in roots:
        arena.tick()
        if totals[root]:return False
    return True
