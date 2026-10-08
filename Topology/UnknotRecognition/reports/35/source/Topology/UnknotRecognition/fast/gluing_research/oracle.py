"""Expanded-sheet topology oracle independent of the compressed kernel.

No gcd, affine composition, spanning-tree gauge, canonical-schema builder,
surface classifier or marked-signature formula is imported here.  Local maps
and peripherals are actual permutation arrays.  The assembled lifted graph
has one vertex for every (piece, sheet), including orientation and labelled
local-generator/seam edges.  Euler characteristic adds across boundary circles.
"""

from collections import Counter, deque


def piece_data(piece, sheets):
    surface = piece['surface']
    orient, genus = surface['orientable'], surface['genus']
    rank_core = 2 * genus if orient else genus
    character = [int(not orient and i < genus) for i in range(len(piece['monodromy']))]
    permutations = [[(m['sign'] * x + m['shift']) % sheets for x in range(sheets)]
                    for m in piece['monodromy']]
    backwards = []
    for perm in permutations:
        inv = [None] * sheets
        for x, y in enumerate(perm):
            inv[y] = x
        backwards.append(inv)
    relation = []
    if orient:
        for i in range(0, rank_core, 2):
            relation.extend([permutations[i], permutations[i + 1],
                             backwards[i], backwards[i + 1]])
    else:
        for i in range(rank_core):
            relation.extend([permutations[i], permutations[i]])
    boundaries = list(permutations[rank_core:])
    relation.extend(boundaries)
    last = [None] * sheets
    for x in range(sheets):
        y = x
        for step in relation:
            y = step[y]
        last[y] = x
    boundaries.append(last)
    chi = 2 - rank_core - surface['boundary_components']
    return dict(maps=permutations, inverses=backwards, character=character,
                boundaries=boundaries, chi=chi)


def compatible(raw, seam):
    """Literal compatibility of the two boundary permutation arrays."""
    n = raw['sheets']
    u, a = seam['left']
    v, b = seam['right']
    left = piece_data(raw['pieces'][u], n)['boundaries'][a]
    right = piece_data(raw['pieces'][v], n)['boundaries'][b]
    if seam['direction'] == -1:
        inv = [None] * n
        for x, y in enumerate(right):
            inv[y] = x
        right = inv
    s, c = seam['map']['sign'], seam['map']['shift']
    mapping = [(s * x + c) % n for x in range(n)]
    return all(mapping[left[x]] == right[mapping[x]] for x in range(n))


def expanded_assembly(raw):
    """Exact finite assembly by explicit lifted-graph traversal and cycles."""
    n, pieces, seams = raw['sheets'], raw['pieces'], raw['seams']
    data = [piece_data(piece, n) for piece in pieces]
    neighbors = [dict() for _ in range(n * len(pieces))]

    def edge(x, y, bit, label, reverse):
        neighbors[x][label] = (y, bit)
        neighbors[y][reverse] = (x, bit)

    for v, piece in enumerate(data):
        for i, (perm, bit) in enumerate(zip(piece['maps'], piece['character'])):
            for x, y in enumerate(perm):
                edge(v * n + x, v * n + y, bit, ('g', v, i, 1), ('g', v, i, -1))
    used = set()
    base_neighbors = [set() for _ in pieces]
    for e, seam in enumerate(seams):
        if not compatible(raw, seam):
            raise ValueError('expanded oracle was given an invalid seam')
        u, a = seam['left']
        v, b = seam['right']
        if (u, a) in used or (v, b) in used or (u, a) == (v, b):
            raise ValueError('expanded oracle was given reused boundaries')
        used.update(((u, a), (v, b)))
        base_neighbors[u].add(v)
        base_neighbors[v].add(u)
        sign, shift = seam['map']['sign'], seam['map']['shift']
        for x in range(n):
            y = (sign * x + shift) % n
            edge(u * n + x, v * n + y, int(seam['direction'] == 1),
                 ('s', e, 1), ('s', e, -1))
    roots, groups = [-1] * len(pieces), {}
    for root in range(len(pieces)):
        if roots[root] != -1:
            continue
        todo, group = [root], []
        roots[root] = root
        while todo:
            u = todo.pop()
            group.append(u)
            for v in base_neighbors[u]:
                if roots[v] == -1:
                    roots[v] = root
                    todo.append(v)
        groups[root] = sorted(group)
    component_of, color = [-1] * len(neighbors), [-1] * len(neighbors)
    components, orientations = [], []
    for start in range(len(neighbors)):
        if component_of[start] != -1:
            continue
        index, found, orient = len(components), [], True
        todo = deque([start])
        component_of[start], color[start] = index, 0
        while todo:
            here = todo.popleft()
            found.append(here)
            for target, bit in neighbors[here].values():
                expected = color[here] ^ bit
                if component_of[target] == -1:
                    component_of[target], color[target] = index, expected
                    todo.append(target)
                elif color[target] != expected:
                    orient = False
        components.append(tuple(sorted(found)))
        orientations.append(orient)
    ports = {root: [(v, b) for v in group for b in range(len(data[v]['boundaries']))
                    if (v, b) not in used] for root, group in groups.items()}
    profiles = [{port: Counter() for port in ports[roots[members[0] // n]]}
                for members in components]
    port_cycles = {}
    for v, piece in enumerate(data):
        for b, perm in enumerate(piece['boundaries']):
            seen, cycles = set(), []
            for x in range(n):
                if x in seen:
                    continue
                cycle, y = [], x
                while y not in seen:
                    seen.add(y)
                    cycle.append(y)
                    if component_of[v * n + y] != component_of[v * n + x]:
                        raise AssertionError('a peripheral cycle escaped its cover component')
                    y = perm[y]
                if y != x:
                    raise AssertionError('a boundary was not a permutation')
                cycles.append(tuple(cycle))
                if (v, b) not in used:
                    profiles[component_of[v * n + x]][v, b][len(cycle)] += 1
            port_cycles[v, b] = cycles
    records = {root: Counter() for root in groups}
    for index, members in enumerate(components):
        counts = Counter(vertex // n for vertex in members)
        root = roots[members[0] // n]
        degree = counts[root]
        if set(counts) != set(groups[root]) or any(c != degree for c in counts.values()):
            raise AssertionError('a component did not cover every base piece in equal degree')
        chi = sum(data[v]['chi'] * counts[v] for v in counts)
        profile = tuple(tuple(sorted(profiles[index][port].items())) for port in ports[root])
        boundaries = sum(sum(profiles[index][port].values()) for port in ports[root])
        orient = orientations[index]
        numerator = 2 - boundaries - chi
        if (orient and (numerator < 0 or numerator % 2)) or (not orient and numerator < 1):
            raise AssertionError('expanded assembly has invalid Euler data')
        genus = numerator // 2 if orient else numerator
        records[root][degree, orient, genus, boundaries, chi, profile] += 1
    return dict(records=records, component_of=component_of, components=components,
                orientations=orientations, neighbors=neighbors, port_cycles=port_cycles,
                roots=roots, groups=groups, remaining_ports=ports)


def compressed_records(summary):
    result = {}
    for base in summary['base_components']:
        records = Counter()
        for family in base['families']:
            profile = tuple(tuple((entry['degree'], entry['multiplicity']) for entry in entries)
                            for entries in family['boundary_lifts'])
            key = (family['cover_degree'], family['orientable'], family['genus'],
                   family['boundary_components'], family['euler_characteristic'], profile)
            records[key] += family['multiplicity']
        result[base['root_piece']] = records
    return result


def rooted_isomorphism(raw, expanded, source, target):
    """Unique rooted cover map by labelled lifted-graph propagation.

    The map preserves base-piece labels and each actual directed edge label.
    It calls no arithmetic classification or gauge/marking routine.
    """
    n = raw['sheets']
    if source[0] != target[0]:
        return None
    start, image = source[0] * n + source[1], target[0] * n + target[1]
    graph = expanded['neighbors']
    mapping, backwards, todo = {start: image}, {image: start}, [start]
    while todo:
        here = todo.pop()
        there = mapping[here]
        if here // n != there // n or graph[here].keys() != graph[there].keys():
            return None
        for label, (x, _) in graph[here].items():
            y = graph[there][label][0]
            if x in mapping:
                if mapping[x] != y:
                    return None
            elif y in backwards:
                return None
            else:
                mapping[x], backwards[y] = y, x
                todo.append(x)
    source_component = expanded['component_of'][start]
    target_component = expanded['component_of'][image]
    if set(mapping) != set(expanded['components'][source_component]):
        return None
    if set(backwards) != set(expanded['components'][target_component]):
        return None
    return mapping
