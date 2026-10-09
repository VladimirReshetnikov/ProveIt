"""Complete optimization in a supplied, explicit layered disk-patch grammar.

Outputs describe ONLY the abstract grammar. They are never knot verdicts.
Each patch is a disk union, represented by its partition of incoming+outgoing
arcs. Every local option is available independently of the current partition.
"""
from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256
from pathlib import Path
import argparse
import json
from envelope_kernel import (Budget, Candidate, DSU, Envelope, ResourceLimit,
    canonical, count, disk_compatible, join, reduce_family, validate)


@dataclass(frozen=True)
class Patch:
    partition: tuple[int, ...]
    cost: int = 0
    sector: int = 0
    def __post_init__(self):
        object.__setattr__(self, "partition", validate(self.partition))
        if type(self.cost) is not int or type(self.sector) is not int or not 0 <= self.sector < 4:
            raise ValueError('invalid patch cost or sector')


@dataclass(frozen=True)
class Grammar:
    widths: tuple[int, ...]
    initial: tuple[Candidate, ...]
    layers: tuple[tuple[Patch, ...], ...]
    caps: tuple[Candidate, ...]
    target_sectors: tuple[int, ...] = (0,)
    def __post_init__(self):
        if not self.widths or any(type(r) is not int or r < 1 for r in self.widths):
            raise ValueError('nonempty positive interface widths required')
        if len(self.layers) + 1 != len(self.widths):
            raise ValueError('wrong number of layers')
        if any(len(x.partition) != self.widths[0] for x in self.initial):
            raise ValueError('initial width mismatch')
        if any(len(x.partition) != self.widths[-1] for x in self.caps):
            raise ValueError('cap width mismatch')
        for i, layer in enumerate(self.layers):
            if any(len(x.partition) != self.widths[i] + self.widths[i + 1] for x in layer):
                raise ValueError('patch width mismatch')
        if (not isinstance(self.target_sectors, tuple) or
            any(type(x) is not int or not 0 <= x < 4 for x in self.target_sectors) or
            len(set(self.target_sectors)) != len(self.target_sectors)):
            raise ValueError('invalid target sectors')


def _item(x):
    return {'partition': list(x.partition), 'cost_hex': hex(x.cost), 'sector': x.sector}


def to_data(g):
    return {'schema': 'layered-disk-patches-v1', 'widths': list(g.widths),
            'initial': [_item(c) for c in g.initial],
            'layers': [[_item(p) for p in layer] for layer in g.layers],
            'caps': [_item(c) for c in g.caps], 'target_sectors': list(g.target_sectors)}


def from_data(data):
    if not isinstance(data, dict) or set(data) != {'schema', 'widths', 'initial', 'layers', 'caps', 'target_sectors'}:
        raise ValueError('unexpected grammar schema fields')
    if data['schema'] != 'layered-disk-patches-v1':
        raise ValueError('unknown grammar schema')
    def parse(x, cls):
        if not isinstance(x, dict) or set(x) != {'partition', 'cost_hex', 'sector'} or not isinstance(x['cost_hex'], str):
            raise ValueError('invalid item schema')
        return cls(tuple(x['partition']), int(x['cost_hex'], 16), x['sector'])
    return Grammar(tuple(data['widths']), tuple(parse(x, Candidate) for x in data['initial']),
                   tuple(tuple(parse(x, Patch) for x in layer) for layer in data['layers']),
                   tuple(parse(x, Candidate) for x in data['caps']), tuple(data['target_sectors']))


def digest(g):
    return sha256(json.dumps(to_data(g), sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def compile_envelopes(g, tick=None):
    """Polynomial union-of-options compiler; does not enumerate assemblies."""
    h = len(g.layers)
    sigma = [join([c.partition for c in g.initial], g.widths[0])]
    for i, options in enumerate(g.layers):
        if tick: tick()
        a, b = g.widths[i:i + 2]
        lifted = sigma[-1] + tuple(count(sigma[-1]) + j for j in range(b))
        coarse = join([lifted] + [p.partition for p in options])
        sigma.append(canonical(coarse[a:]))
    rho = [None] * (h + 1)
    rho[h] = join([c.partition for c in g.caps], g.widths[-1])
    for i in range(h - 1, -1, -1):
        if tick: tick()
        a, b = g.widths[i:i + 2]
        lifted = tuple(range(a)) + tuple(a + x for x in rho[i + 1])
        coarse = join([lifted] + [p.partition for p in g.layers[i]])
        rho[i] = canonical(coarse[:a])
    return tuple(sigma), tuple(rho)


def transition(p, patch, out_width, tick=None):
    r, a, b = len(p), count(p), count(patch)
    dsu = DSU(a + b)
    for e in range(r):
        if tick: tick()
        if not dsu.union(p[e], a + patch[e]):
            return None
    output_roots = [dsu.find(a + patch[r + j]) for j in range(out_width)]
    if set(output_roots) != {dsu.find(v) for v in range(a + b)}:
        return None
    return canonical(output_roots)


def deduplicate(items):
    best = {}
    for c in items:
        key = (c.partition, c.sector)
        if key not in best or (c.cost, c.witness) < (best[key].cost, best[key].witness):
            best[key] = c
    return sorted(best.values(), key=lambda c: (c.partition, c.sector))


def solve(g, mode='cycle', *, tick=None, max_cycle_rank=18, max_root_width=20):
    if mode not in ('exact', 'root', 'cycle'):
        raise ValueError('unknown solver mode')
    if tick: tick()
    sigma, rho = compile_envelopes(g, tick)
    # Exact/root comparators need no cycle features and must not be artificially
    # constrained by the new engine's allocation guard.
    envelopes = [Envelope(s, t, max_cycle_rank if mode == 'cycle' else None, tick)
                 for s, t in zip(sigma, rho)]
    stages, stats = [], []
    items = [Candidate(c.partition, c.cost, c.sector, (j,)) for j, c in enumerate(g.initial)]
    for i in range(len(g.widths)):
        if tick: tick()
        env = envelopes[i]
        raw = len(items)
        items = deduplicate(items)
        # Safe and identical connectivity prefilter in all three modes.
        items = [c for c in items if env.viable(c.partition)]
        before = len(items)
        if mode == 'exact':
            certificate = {'schema': 'exact-dedup-v1', 'retained': list(range(len(items)))}
        else:
            reduced = reduce_family(items, env, mode=mode, tick=tick, max_root_width=max_root_width)
            certificate = reduced.certificate
            items = [items[j] for j in reduced.retained]
        stages.append(certificate)
        stats.append({'interface': i, 'arcs': g.widths[i], 'cycle_rank': env.lam,
                      'generated': raw, 'viable_distinct': before, 'retained': len(items)})
        if i < len(g.layers):
            following = []
            for c in items:
                for j, option in enumerate(g.layers[i]):
                    if tick: tick()
                    p = transition(c.partition, option.partition, g.widths[i + 1], tick)
                    if p is not None:
                        following.append(Candidate(p, c.cost + option.cost, c.sector ^ option.sector,
                                                   c.witness + (j,)))
            items = following
    best = None
    for c in items:
        for j, cap in enumerate(g.caps):
            if tick: tick()
            if c.sector ^ cap.sector in g.target_sectors and disk_compatible(c.partition, cap.partition):
                entry = (c.cost + cap.cost, c.witness + (j,), c.sector ^ cap.sector)
                if best is None or entry < best:
                    best = entry
    result = {'schema': 'cycle-envelope-run-v1', 'grammar_sha256': digest(g), 'mode': mode,
              'status': 'FOUND_ABSTRACT_DISK' if best is not None else 'NO_DISK_IN_GRAMMAR',
              'cost_hex': None if best is None else hex(best[0]),
              'witness': None if best is None else list(best[1]),
              'sector': None if best is None else best[2], 'stages': stages, 'statistics': stats}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('grammar', type=Path)
    parser.add_argument('--mode', choices=('exact', 'root', 'cycle'), default='cycle')
    parser.add_argument('--seconds', type=float)
    parser.add_argument('--steps', type=int)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        g = from_data(json.loads(args.grammar.read_text()))
        result = solve(g, args.mode, tick=Budget(args.seconds, args.steps))
    except ResourceLimit as exc:
        result = {'status': 'RESOURCE_LIMIT', 'reason': str(exc)}
    output = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(output)
    else:
        print(output, end='')

if __name__ == '__main__':
    main()
