"""Exact survivor transfer restricted to relevant paths, in either direction.

The scalar contraction convention is frozen from the previous graded-transfer
prototype.  The new kernel expresses each adjacent-degree differential as the
path sum of a typed acyclic graph, removes vertices outside all survivor paths,
and chooses a propagation direction separately for each remaining component.

Inputs must be valid quantum-homogeneous complexes in the scanner's cobordism
category.  This is an exact optional reducer, not an a priori complexity bound
on the number of objects created by scanning a knot diagram.
"""
from __future__ import annotations

from collections import defaultdict

from .binary_contraction import binary_contraction, bits, xor_entry
from .graded import GradedScan
from .scan_fast import FastScan


def _indices(column):
    return bits(column) if isinstance(column, int) else iter(column)


def _build_graph(scan, scalar, degree, original, survivors):
    """Build z --delta--> w --H--> z, with scalar input/output edges."""
    node_ids, matching, quantum, kind, label = {}, [], [], [], []
    outgoing, incoming = [], []

    def node(tag, ident, ma, q):
        index = len(matching)
        node_ids[tag, ident] = index
        matching.append(ma)
        quantum.append(q)
        kind.append(tag)
        label.append(ident)
        outgoing.append([])
        incoming.append([])
        return index

    for a in original.get(degree, ()):
        node('z', a, scan.mid[a], scan.qshift[a])
    for b in original.get(degree + 1, ()):
        node('w', b, scan.mid[b], scan.qshift[b])
    inputs = [node('s', s, scalar['mid'][s], scalar['q'][s])
              for s in survivors.get(degree, ())]
    outputs = [node('t', t, scalar['mid'][t], scalar['q'][t])
               for t in survivors.get(degree + 1, ())]

    def edge(a, b, value, geometric=False):
        outgoing[a].append((b, value, geometric))
        incoming[b].append((a, value, geometric))

    for a in original.get(degree, ()):
        scan._check()
        for b, value in scan.out[a].items():
            if scan.deg[b] != degree + 1:
                raise ArithmeticError('differential changes homological degree incorrectly')
            if scan.qshift[b] < scan.qshift[a]:
                raise ArithmeticError('negative intrinsic weight in graded input')
            if scan.qshift[b] > scan.qshift[a]:
                edge(node_ids['z', a], node_ids['w', b], value, True)
    for b in original.get(degree + 1, ()):
        for a in _indices(scalar['h'][b]):
            edge(node_ids['w', b], node_ids['z', a], 1)
        for t in _indices(scalar['p'][b]):
            edge(node_ids['w', b], node_ids['t', t], 1)
    for s in survivors.get(degree, ()):
        for a in _indices(scalar['i'][s]):
            edge(node_ids['s', s], node_ids['z', a], 1)

    phase = {'w': 0, 's': 1, 'z': 2, 't': 3}
    order = sorted(range(len(matching)), key=lambda a: (quantum[a], phase[kind[a]], a))
    position = {a: j for j, a in enumerate(order)}
    for a, row in enumerate(outgoing):
        for b, value, geometric in row:
            if position[a] >= position[b]:
                raise ArithmeticError('transfer support is not acyclic')
            if not geometric and matching[a] != matching[b]:
                raise ArithmeticError('scalar contraction changed matching type')
    return dict(matching=matching, quantum=quantum, kind=kind, label=label,
                out=outgoing, inc=incoming, order=order, inputs=inputs, outputs=outputs)


def _reachability(graph, check):
    """Packed endpoint reach sets.  These are structural, not numerical ranks."""
    n = len(graph['matching'])
    forward, backward = [0] * n, [0] * n
    for j, a in enumerate(graph['inputs']):
        forward[a] = 1 << j
    for a in graph['order']:
        check()
        mask = forward[a]
        if mask:
            for b, _, _ in graph['out'][a]:
                forward[b] |= mask
    for j, b in enumerate(graph['outputs']):
        backward[b] = 1 << j
    for b in reversed(graph['order']):
        check()
        mask = backward[b]
        if mask:
            for a, _, _ in graph['inc'][b]:
                backward[a] |= mask
    return forward, backward


def _boolean_reachability(graph, check):
    """Only two flags per vertex; used with the coarser endpoint-count bound."""
    forward = [False] * len(graph['matching'])
    backward = [False] * len(graph['matching'])
    for a in graph['inputs']:
        forward[a] = True
    for a in graph['order']:
        check()
        if forward[a]:
            for b, _, _ in graph['out'][a]:
                forward[b] = True
    for b in graph['outputs']:
        backward[b] = True
    for b in reversed(graph['order']):
        check()
        if backward[b]:
            for a, _, _ in graph['inc'][b]:
                backward[a] = True
    return forward, backward


def _components(graph, active, check):
    """Weak components include terminals, so resulting matrix blocks are disjoint."""
    parent = list(range(len(active)))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for a, row in enumerate(graph['out']):
        if not active[a]:
            continue
        check()
        for b, _, _ in row:
            if active[b]:
                ra, rb = find(a), find(b)
                if ra != rb:
                    parent[rb] = ra
    grouped = defaultdict(list)
    for a in graph['order']:
        if active[a]:
            grouped[find(a)].append(a)
    return list(grouped.values())


def corridor_transfer(scan, *, mode='auto', prune=True,
                      direction_policy='reach', scalar_engine='global'):
    """Return the full minimal differential, without changing scan objects/maps.

    mode is 'forward', 'reverse', or 'auto'.  Auto minimizes an exact structural
    bound on coefficient edge propagations, separately for each weak component.
    prune=False is a diagnostic ablation: forward propagation then evaluates
    every reachable branch, including branches that do not reach a survivor.
    Scalar contraction setup and reach-mask construction are included in the
    implementation's total cost; the direction bound is not a runtime oracle.

    direction_policy='ports' uses Boolean flags and the number of terminals,
    avoiding packed endpoint sets. scalar_engine='components' contracts each
    scalar graph component locally and retains sparse scalar matrix columns.
    The two defaults retain the frozen predecessor's setup for controlled
    comparisons; these parameters change representation, not the result.
    """
    if mode not in ('auto', 'forward', 'reverse'):
        raise ValueError('mode must be auto, forward, or reverse')
    if direction_policy not in ('reach', 'ports'):
        raise ValueError('direction_policy must be reach or ports')
    if scalar_engine not in ('global', 'components'):
        raise ValueError('scalar_engine must be global or components')
    scan._check()
    if scalar_engine == 'components':
        from .scalar_components import component_contraction
        scalar = component_contraction(scan)
    else:
        scalar = binary_contraction(scan)
    original, survivors = defaultdict(list), defaultdict(list)
    for a, ma in enumerate(scan.mid):
        if ma is not None:
            original[scan.deg[a]].append(a)
    for s, h in enumerate(scalar['deg']):
        survivors[h].append(s)
    result_out = [{} for _ in scalar['mid']]
    stats = dict(graph_vertices=0, graph_edges=0, retained_vertices=0,
                 retained_edges=0, components=0, forward_components=0,
                 reverse_components=0, forward_bound=0, reverse_bound=0,
                 chosen_bound=0, propagations=0, geometric_propagations=0,
                 compositions=0, coefficient_xors=0, skipped_degree_pairs=0)
    details = []

    def multiply(source_ma, middle_ma, target_ma, first, second):
        if first == 1 and source_ma == middle_ma:
            return second
        if second == 1 and middle_ma == target_ma:
            return first
        stats['compositions'] += 1
        key = (source_ma, middle_ma, target_ma, first, second)
        value = scan.composed.get(key)
        if value is None:
            value = scan._compose(key)
        return value

    for degree in sorted(original):
        if not survivors.get(degree) or not survivors.get(degree + 1):
            stats['skipped_degree_pairs'] += 1
            continue
        graph = _build_graph(scan, scalar, degree, original, survivors)
        reachability = _reachability if direction_policy == 'reach' else _boolean_reachability
        forward, backward = reachability(graph, scan._check)
        active = ([bool(a and b) for a, b in zip(forward, backward)]
                  if prune else [True] * len(forward))
        out, inc, ma = graph['out'], graph['inc'], graph['matching']
        stats['graph_vertices'] += len(ma)
        stats['graph_edges'] += sum(map(len, out))
        stats['retained_vertices'] += sum(active)
        stats['retained_edges'] += sum(active[a] and active[b]
                                      for a, row in enumerate(out) for b, _, _ in row)
        for component in _components(graph, active, scan._check):
            keep = set(component)
            inputs = [a for a in component if graph['kind'][a] == 's']
            outputs = [a for a in component if graph['kind'][a] == 't']
            # Dead diagnostic components may have just one kind of terminal.
            if not inputs and not outputs:
                continue
            f_bound = r_bound = 0
            for a in component:
                for b, _, _ in out[a]:
                    if b in keep:
                        f_bound += (forward[a].bit_count() if direction_policy == 'reach'
                                    else len(inputs))
                        r_bound += (backward[b].bit_count() if direction_policy == 'reach'
                                    else len(outputs))
            direction = ('forward' if f_bound <= r_bound else 'reverse') if mode == 'auto' else mode
            stats['components'] += 1
            stats[direction + '_components'] += 1
            stats['forward_bound'] += f_bound
            stats['reverse_bound'] += r_bound
            stats['chosen_bound'] += f_bound if direction == 'forward' else r_bound
            details.append(dict(degree=degree, vertices=len(component), sources=len(inputs),
                                targets=len(outputs), forward_bound=f_bound,
                                reverse_bound=r_bound, direction=direction))
            if direction == 'forward':
                for start in inputs:
                    scan._check()
                    values = {start: 1}
                    source = graph['label'][start]
                    source_ma = ma[start]
                    for a in component:
                        value = values.pop(a, 0)
                        if not value:
                            continue
                        if graph['kind'][a] == 't':
                            xor_entry(result_out[source], graph['label'][a], value)
                            continue
                        for b, edge_value, geometric in out[a]:
                            if b not in keep:
                                continue
                            stats['propagations'] += 1
                            product = value
                            if geometric:
                                stats['geometric_propagations'] += 1
                                product = multiply(source_ma, ma[a], ma[b], value, edge_value)
                            xor_entry(values, b, product)
                            stats['coefficient_xors'] += bool(product)
                        scan._check()
            else:
                for end in outputs:
                    scan._check()
                    values = {end: 1}
                    target = graph['label'][end]
                    target_ma = ma[end]
                    for b in reversed(component):
                        value = values.pop(b, 0)
                        if not value:
                            continue
                        if graph['kind'][b] == 's':
                            xor_entry(result_out[graph['label'][b]], target, value)
                            continue
                        for a, edge_value, geometric in inc[b]:
                            if a not in keep:
                                continue
                            stats['propagations'] += 1
                            product = value
                            if geometric:
                                stats['geometric_propagations'] += 1
                                product = multiply(ma[a], ma[b], target_ma, edge_value, value)
                            xor_entry(values, a, product)
                            stats['coefficient_xors'] += bool(product)
                        scan._check()
    scan._check()
    if stats['propagations'] > stats['chosen_bound']:
        raise ArithmeticError('actual propagation count exceeds structural bound')
    return dict(mid=scalar['mid'], deg=scalar['deg'], q=scalar['q'], out=result_out,
                scalar=scalar, stats=stats, components=details,
                direction_policy=direction_policy, scalar_engine=scalar_engine)


# Short name for standalone kernel experiments.
transfer = corridor_transfer


class CorridorScan(GradedScan):
    """Production-compatible optional scanner using complete corridor transfer."""

    def __init__(self, *args, mode='auto', prune=True,
                 direction_policy='reach', scalar_engine='global', **kwargs):
        super().__init__(*args, **kwargs)
        if mode not in ('auto', 'forward', 'reverse'):
            raise ValueError('mode must be auto, forward, or reverse')
        self.corridor_mode, self.corridor_prune = mode, prune
        if direction_policy not in ('reach', 'ports'):
            raise ValueError('direction_policy must be reach or ports')
        if scalar_engine not in ('global', 'components'):
            raise ValueError('scalar_engine must be global or components')
        self.direction_policy, self.scalar_engine = direction_policy, scalar_engine
        self.stats.update(corridor_stages=0, corridor_peak_survivors=0)
        self.history = []

    def eliminate(self, *, update_budget=None):
        if update_budget is not None:
            return FastScan.eliminate(self, update_budget=update_budget)
        before = self.live
        result = corridor_transfer(self, mode=self.corridor_mode, prune=self.corridor_prune,
                                   direction_policy=self.direction_policy, scalar_engine=self.scalar_engine)
        # Install only after all required products and resource checks succeed.
        self.mid, self.deg, self.qshift, self.out = (
            result['mid'], result['deg'], result['q'], result['out'])
        self.live = len(self.mid)
        self.inc = [set() for _ in self.mid]
        for a, row in enumerate(self.out):
            for b in row:
                self.inc[b].add(a)
        self.composed = {}
        self.stats['eliminations'] += (before - self.live) // 2
        self.stats['compositions'] += result['stats']['compositions']
        self.stats['corridor_stages'] += 1
        self.stats['corridor_peak_survivors'] = max(self.stats['corridor_peak_survivors'], self.live)
        for name, value in result['stats'].items():
            key = 'corridor_' + name
            self.stats[key] = self.stats.get(key, 0) + value
        self.history.append(dict(before=before, survivors=self.live, **result['stats']))
        return True


class AdaptiveCorridorScan(CorridorScan):
    """Retain completed sparse pivots, then use complete transfer if needed."""

    def eliminate(self, *, update_budget=None):
        if update_budget is not None:
            return FastScan.eliminate(self, update_budget=update_budget)
        allowance = max(256, 4 * self.live)
        if FastScan.eliminate(self, update_budget=allowance):
            return True
        self.stats['corridor_switches'] = self.stats.get('corridor_switches', 0) + 1
        return CorridorScan.eliminate(self)
