"""One-sided randomized search; every positive is independently replayed.

UNKNOWN is not a negative answer. Fixed PRNG seeds are for reproducibility,
not derandomization. Caps bound this kernel, never native geometry preparation.
"""
from __future__ import annotations
from collections import deque
import random
import secrets
from .model import Instance, extend_tree, peel
from .closure import Activation
from .matroid import representatives
from .algebra import choose_prime, sample_representation, wedge_extend, ExteriorBasis, incidence_vectors
from .verify import verify_positive, verify_obstruction


class WorkLimit(Exception):
    pass


def positive_certificate(inst: Instance, tree: list[int]) -> dict:
    pivots = peel(inst, tree)
    if pivots is None:
        raise AssertionError('constructed forest does not complete peeling')
    adj = [[] for _ in range(inst.vertices)]
    for e in tree:
        u, v = inst.edges[e]
        adj[u].append((v, e))
        adj[v].append((u, e))
    seen, queue, order = {0}, deque([0]), []
    while queue:
        for v, e in sorted(adj[queue.popleft()]):
            if v not in seen:
                seen.add(v)
                queue.append(v)
                order.append([e, v])
    cert = dict(schema='activation-forest-positive-v1', input_sha256=inst.digest(),
                tree=tree, dual_order=order, pivots=pivots)
    if not verify_positive(inst, cert):
        raise AssertionError('independent local replay failed')
    return cert


def search_projected(act: Activation, vectors, p: int, *,
                     max_transitions: int | None = None, check=lambda: None,
                     reduce_families: bool = True, record_frontier: bool = False):
    """Exact in the supplied sampled representation; returns seeds or None.

    reduce_families=False is a deduplicated literal-set-family research control, not a recommended
    production path. Both modes preserve actual raw wedge witnesses.
    """
    stats = dict(transitions=0, nonzero=0, retained=1, discarded=0, states=1, peak_basis=1)
    initial = act.close(0)
    if initial == act.full:
        return (), stats
    seed_basis = ExteriorBasis(p)
    seed_basis.add({0: 1}, ())
    current = {initial: seed_basis}
    if record_frontier:
        stats['frontier'] = [dict(mask=initial, size=0, seeds=[[]])]
    for k in range(act.b):
        following = {}
        for mask in sorted(current):
            for raw, chosen in current[mask].witnesses:
                for e, vector in enumerate(vectors):
                    check()
                    if max_transitions is not None and stats['transitions'] >= max_transitions:
                        raise WorkLimit(stats)
                    stats['transitions'] += 1
                    target = act.close(mask | act.masks[e])
                    if target == mask:
                        continue
                    ext = wedge_extend(raw, vector, p)
                    if not ext:
                        continue
                    stats['nonzero'] += 1
                    new = (*chosen, e)
                    if target == act.full:
                        return new, stats
                    if target not in following:
                        following[target] = ExteriorBasis(p)
                        stats['states'] += 1
                    basis = following[target]
                    if reduce_families:
                        accepted = basis.add(ext, new)
                    else:
                        key = tuple(sorted(new))
                        accepted = key not in basis.seen_sets
                        if accepted:
                            basis.seen_sets.add(key)
                            basis.witnesses.append((ext, new))
                    stats['retained'] += accepted
                    stats['discarded'] += not accepted
                    stats['peak_basis'] = max(stats['peak_basis'], len(basis.witnesses))
        if record_frontier:
            stats['frontier'].extend(dict(mask=s, size=k+1,
                                         seeds=[list(x) for _, x in basis.witnesses])
                                     for s, basis in sorted(following.items()))
        current = following
        if not current:
            break
    return None, stats


def solve(inst: Instance, *, rounds: int = 8, seed: int | None = None,
          max_b: int | None = 20, max_transitions: int | None = 1_000_000,
          try_incumbent: bool = True, check=lambda: None) -> dict:
    if type(rounds) is not int or rounds < 0:
        raise ValueError('rounds must be a nonnegative integer')
    for cap in (max_b, max_transitions):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError('caps must be nonnegative integers or None')
    if seed is not None and type(seed) is not int:
        raise ValueError('seed must be an integer or None')
    check()
    if inst.m == 0:
        return dict(status='SUCCESS', route='empty', certificate=positive_certificate(inst, []), stats={})
    if try_incumbent:
        tree = extend_tree(inst, ())
        if peel(inst, tree) is not None:
            return dict(status='SUCCESS', route='incumbent',
                        certificate=positive_certificate(inst, tree), stats={})
    act = Activation(inst)
    check()
    stats = dict(boundary_rows=act.b, mandatory_blocks=len(act.mandatory), rounds=[],
                 sampling='system-random' if seed is None else 'fixed-prng-reproduction')
    pre = representatives(inst, act.mandatory)
    if not pre['complete']:
        cert = dict(schema='activation-mandatory-obstruction-v1', input_sha256=inst.digest(),
                    blocks=[sorted(act.mandatory[i]) for i in pre['obstruction_colors']])
        if not verify_obstruction(inst, cert):
            raise AssertionError('independent mandatory obstruction replay failed')
        return dict(status='BLOCKED_EXACT', route='mandatory-rank', obstruction=cert, stats=stats)
    if act.close(0) == act.full:
        tree = extend_tree(inst, pre['edges'])
        return dict(status='SUCCESS', route='automatic-closure',
                    certificate=positive_certificate(inst, tree), stats=stats)
    if max_b is not None and act.b > max_b:
        return dict(status='UNKNOWN', reason='exceptional-boundary cap', stats=stats)
    q, b = len(act.mandatory), act.b
    # In this special regime the original binary incidence representation is
    # faithful and already has rank at most b: no randomization is needed.
    if q == 0 and inst.vertices - 1 <= b:
        vectors = incidence_vectors(inst, 2)
        try:
            chosen, trial = search_projected(act, vectors, 2, max_transitions=max_transitions,
                                              check=check, record_frontier=True)
        except WorkLimit as error:
            trial = error.args[0]
            trial.pop('frontier', None)
            stats['rounds'].append(trial)
            return dict(status='UNKNOWN', reason='transition cap', stats=stats)
        frontier = trial.pop('frontier', [])
        stats['rounds'].append(trial)
        stats['sampling'] = 'none-faithful-binary-incidence'
        if chosen is not None:
            tree = extend_tree(inst, chosen)
            return dict(status='SUCCESS', route='faithful-activation', seeds=list(chosen),
                        certificate=positive_certificate(inst, tree), stats=stats)
        cert = dict(schema='activation-frontier-obstruction-v1', input_sha256=inst.digest(),
                    frontier=frontier)
        if not verify_obstruction(inst, cert):
            raise AssertionError('independent faithful-frontier replay failed')
        return dict(status='BLOCKED_EXACT', route='faithful-frontier', obstruction=cert, stats=stats)
    p = choose_prime(q, b)
    stats['prime'] = p
    rng = secrets.SystemRandom() if seed is None else random.Random(seed)
    remaining = max_transitions
    for attempt in range(rounds):
        check()
        vectors = sample_representation(inst, act.mandatory, b, p, rng)
        if vectors is None:
            stats['rounds'].append(dict(mandatory_rank_lost=True))
            continue
        try:
            chosen, trial = search_projected(act, vectors, p, max_transitions=remaining, check=check)
        except WorkLimit as error:
            trial = error.args[0]
            trial.pop('frontier', None)
            stats['rounds'].append(trial)
            return dict(status='UNKNOWN', reason='transition cap', stats=stats)
        stats['rounds'].append(trial)
        if remaining is not None:
            remaining -= trial['transitions']
        if chosen is None:
            continue
        genuine = representatives(inst, act.mandatory, fixed=chosen)
        if not genuine['complete']:
            raise AssertionError('sampled independent set had no genuine extension')
        tree = extend_tree(inst, (*chosen, *genuine['edges']))
        return dict(status='SUCCESS', route='representative-activation',
                    seeds=list(chosen), mandatory_representatives=genuine['edges'],
                    certificate=positive_certificate(inst, tree), stats=stats)
    return dict(status='UNKNOWN', reason='sampling rounds exhausted', stats=stats)
