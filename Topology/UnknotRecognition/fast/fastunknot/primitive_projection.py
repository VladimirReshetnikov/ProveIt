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


def projection_candidates(arena, roots, alive, cache=None):
    """One current-slot snapshot with immutable structural eligibility cached.

    Slot numbers and live membership are rebuilt every time. Only word content
    is cached; normalization and substitution create new roots when it changes.
    """
    if cache is None:cache = {}
    records = cache.setdefault('candidates',{0:None})
    # Charge both complete slot scans before constructing their temporary lists.
    arena.tick(2*len(roots)+1)
    fresh = list(dict.fromkeys(root for root in roots if root not in records))
    meta,powers = projection_metadata(arena,fresh,cache)
    for root in fresh:
        arena.tick();counts = meta[root]
        if counts is None or len(counts)!=2 or any(p and n for p,n in counts.values()):
            records[root] = None
        else:
            pair = tuple(sorted(counts))
            records[root] = pair,tuple(counts[g][0]-counts[g][1] for g in pair)
        arena.stats['projection_candidate_roots'] = arena.stats.get('projection_candidate_roots',0)+1
    candidates = [(slot,root,records[root]) for slot,root in enumerate(roots)
                  if records[root] is not None and all(g in alive for g in records[root][0])]
    arena.stats['projection_candidate_slots'] = arena.stats.get('projection_candidate_slots',0)+len(candidates)
    return candidates,powers


def plan_projection(arena, roots, alive, cache=None, *, _prepared=None):
    """Select disjoint coherent donors from a current structural snapshot."""
    candidates,powers = projection_candidates(arena,roots,alive,cache) if _prepared is None else _prepared
    selected,used = [],set()
    for slot,root,(pair,vector) in candidates:
        arena.tick()
        if used.intersection(pair):continue
        if min(abs(x) for x in vector)==1:
            # A coherent word with a single occurrence of one generator is
            # primitive, regardless of the other generator's exponent.
            evidence = dict(kind='rank_two_primitive_power',relation=slot,generators=list(pair),
                            primitive_vector=list(vector),exponent=1,width=sum(abs(x) for x in vector)-1)
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
