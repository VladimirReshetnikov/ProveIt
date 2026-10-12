"""Sparse scalar contraction with the frozen predecessor's exact basis.

The weight-zero differential splits into weak graph components.  Computing its
binary contraction independently on those components avoids global object-bit
masks for many disconnected identity pairs.  Output columns are sorted tuples
of indices, including empty tuples on dead slots.  The returned i/p/h maps are
entrywise identical to the frozen dense-mask convention after tuple-to-mask
conversion; survivor ordering is restored by each kernel representative's
largest original support index.
"""
from collections import defaultdict
from types import SimpleNamespace

from .graded_transfer import binary_contraction, bits


def sparse_binary_contraction(scan):
    """Return a typed special contraction of the scalar differential.

    One-vertex components and single scalar-arrow components have direct sparse
    contractions.  Every other component uses the inherited exact local binary
    algorithm.  The input must be a valid quantum-homogeneous scan complex.
    No scan objects or differential maps are modified.
    """
    scan._check()
    slots = len(scan.mid)
    live = [a for a, matching in enumerate(scan.mid) if matching is not None]
    parent = {a: a for a in live}
    sizes = {a: 1 for a in live}
    scalar_out = {a: [] for a in live}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    scalar_edges = 0
    for a in live:
        scan._check()
        for b, value in scan.out[a].items():
            if scan.qshift[b] != scan.qshift[a]:
                continue
            if (scan.mid[b] != scan.mid[a] or value != 1
                    or scan.deg[b] != scan.deg[a] + 1):
                raise ArithmeticError('weight-zero map is not a typed scalar differential')
            scalar_out[a].append(b)
            scalar_edges += 1
            ra, rb = find(a), find(b)
            if ra != rb:
                if sizes[ra] < sizes[rb]:
                    ra, rb = rb, ra
                parent[rb] = ra
                sizes[ra] += sizes[rb]

    grouped = defaultdict(list)
    for a in live:
        grouped[find(a)].append(a)
    components = list(grouped.values())
    # These provisional survivor numbers are remapped once all local bases
    # have been computed.  p/h are sparse columns on the original object slots.
    records = []
    p_cols = [()] * slots
    h_cols = [()] * slots
    stats = dict(components=len(components), scalar_edges=scalar_edges,
                 singleton_components=0, pair_components=0,
                 binary_components=0, binary_vertices=0, largest_component=0,
                 local_cubic_bound=0)

    def survivor(a, support):
        records.append((scan.mid[a], scan.deg[a], scan.qshift[a], support))
        return len(records) - 1

    for component in components:
        scan._check()
        count = len(component)
        stats['largest_component'] = max(stats['largest_component'], count)
        if count == 1:
            a = component[0]
            if scalar_out[a]:
                raise ArithmeticError('scalar singleton contains a self arrow')
            p_cols[a] = (survivor(a, (a,)),)
            stats['singleton_components'] += 1
            continue
        if count == 2:
            arrows = [(a, b) for a in component for b in scalar_out[a]]
            if len(arrows) == 1:
                a, b = arrows[0]
                h_cols[b] = (a,)
                stats['pair_components'] += 1
                continue

        stats['binary_components'] += 1
        stats['binary_vertices'] += count
        stats['local_cubic_bound'] += count ** 3
        local_index = {a: j for j, a in enumerate(component)}
        local = SimpleNamespace(
            mid=[scan.mid[a] for a in component],
            deg=[scan.deg[a] for a in component],
            qshift=[scan.qshift[a] for a in component],
            out=[{local_index[b]: 1 for b in scalar_out[a]} for a in component],
            _check=scan._check,
        )
        contraction = binary_contraction(local)
        offset = len(records)
        for index, mask in enumerate(contraction['i']):
            support = tuple(component[j] for j in bits(mask))
            if not support:
                raise ArithmeticError('empty scalar homology representative')
            records.append((contraction['mid'][index], contraction['deg'][index],
                            contraction['q'][index], support))
        for j, a in enumerate(component):
            p_cols[a] = tuple(offset + s for s in bits(contraction['p'][j]))
            h_cols[a] = tuple(component[b] for b in bits(contraction['h'][j]))

    # Local column elimination sees the same increasing source and target
    # orders as the original global algorithm.  Its selected kernel vectors
    # have distinct largest source indices (their original dependent columns).
    anchors = [None] * slots
    for s, record in enumerate(records):
        anchor = record[3][-1]
        if anchors[anchor] is not None:
            raise ArithmeticError('scalar kernel representatives share an anchor')
        anchors[anchor] = s
    survivor_groups = defaultdict(list)
    for s in anchors:
        if s is not None:
            matching, degree, quantum, _ = records[s]
            survivor_groups[matching, quantum, degree].append(s)
    order = [s for key in sorted(survivor_groups) for s in survivor_groups[key]]
    stats['survivor_groups'] = len(survivor_groups)
    new_index = [0] * len(records)
    for index, old in enumerate(order):
        new_index[old] = index
    for a in live:
        p_cols[a] = tuple(sorted(new_index[s] for s in p_cols[a]))
    i_cols = [records[s][3] for s in order]
    result = dict(i=i_cols, p=p_cols, h=h_cols,
                  mid=[records[s][0] for s in order],
                  deg=[records[s][1] for s in order],
                  q=[records[s][2] for s in order])
    stats['i_entries'] = sum(map(len, i_cols))
    stats['p_entries'] = sum(map(len, p_cols))
    stats['h_entries'] = sum(map(len, h_cols))
    result['stats'] = stats
    scan._check()
    return result


component_contraction = sparse_binary_contraction
