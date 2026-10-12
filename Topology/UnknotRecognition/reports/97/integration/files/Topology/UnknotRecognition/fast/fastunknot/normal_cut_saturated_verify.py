"""Independent replay of source-bound saturated-bundle census certificates.

Imports no saturated producer, its forest builder, row constructor, planner,
or census routine.  Source-orbit verification remains delegated to the
established independent source checkers.
"""

from collections import Counter

from .integer_codec import encoded_integer, certificate_equal
from .normal_parallelity_verify import verify_normal_cut_parallelity
from .parallelity_boundary_words_verify import verify_parallelity_boundary_words


class _CallbackFailure(Exception):
    pass


def _decode(x):
    if isinstance(x, dict):
        return {k: _decode(v) for k, v in x.items()}
    if isinstance(x, list):
        return [_decode(v) for v in x]
    if isinstance(x, str) and x.lower().lstrip('+-').startswith('0x'):
        return encoded_integer(x)
    return x


def _int(x):
    if type(x) is not int:
        raise ValueError('expected exact integer')
    return x


def _components_and_forest(core, supplied, check):
    n = len(core['handles0'])
    adjacency = [[] for _ in range(n)]
    for h in core['handles1']:
        a, b = h['ends']
        adjacency[a].append(b)
        adjacency[b].append(a)
    labels = [None] * n
    for start in range(n):
        if labels[start] is not None:
            continue
        labels[start] = start
        todo = [start]
        while todo:
            check()
            for v in adjacency[todo.pop()]:
                if labels[v] is None:
                    labels[v] = start
                    todo.append(v)
    if type(supplied) is not list:
        return None
    forest = [_int(v) for v in supplied]
    if len(set(forest)) != len(forest):
        return None
    parent = list(range(n))

    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v

    for h in forest:
        check()
        if not 0 <= h < len(core['handles1']):
            return None
        a, b = map(root, core['handles1'][h]['ends'])
        if a == b:
            return None
        parent[b] = a
    if len(forest) != n-len(set(labels)):
        return None
    return labels, set(forest)


def _walk(g, letters, check):
    pieces, handles = [], []
    for letter in letters:
        check()
        p = g['ports'][abs(letter)-1]
        h = p['core_handle']
        if p['core_dimension'] == 0:
            pieces.append((h, h))
            continue
        if p['core_dimension'] != 1:
            raise ValueError('invalid annular port')
        poly = g['polygons'][p['polygon']]
        edge = p['edge']
        if poly['kind'] != 'edge_cap' or poly['edges'][edge]['kind'] != 'face_sector':
            raise ValueError('annular port lacks a face-sector chart')
        data = g['core']['handles1'][h]
        lookup = {(data['tetrahedron'], data['face']): 0,
                  (data['target_tetrahedron'], data['target_face']): 1}
        if len(lookup) != 2:
            raise ValueError('non-distinct source face flags')
        points = [poly['vertices'][(edge+j) % len(poly['vertices'])] for j in (0, 1)]
        directions = [lookup.get((v['tetrahedron'], v['face'])) for v in points]
        if None in directions or sorted(directions) != [0, 1]:
            raise ValueError('annular crossing has invalid endpoint charts')
        if letter < 0:
            directions.reverse()
        pieces.append(tuple(data['ends'][d] for d in directions))
        handles.append(h)
    if not pieces or any(stop != pieces[(j+1) % len(pieces)][0]
                         for j, (_, stop) in enumerate(pieces)):
        raise ValueError('annular source path does not close')
    return handles


def replay_saturated_source_census(g, summary, skeleton, certificate, *, check=lambda: None):
    """Finite replay after independent authentication of all three source objects."""
    check()
    callback = check

    def check():
        try:
            callback()
        except Exception as error:
            raise _CallbackFailure(error) from error

    try:
        cert = _decode(certificate)
        if type(cert) is not dict or set(cert) != {
                'schema', 'forest', 'saturated_bases', 'cancellations', 'census'}:
            return False
        if cert['schema'] != 'saturated-source-census-v1':
            return False
        core, profiles = g['core'], summary['base_profiles']
        if core['handles3'] or any(p['boundary_components'] <= 0 for p in profiles):
            return False
        connected = _components_and_forest(core, cert['forest'], check)
        if connected is None:
            return False
        component, forest = connected
        owner = {}
        for i, p in enumerate(profiles):
            for port in p['core_ports']:
                if port in owner or p['multiplicity'] != 1:
                    return False
                owner[port] = i
        if set(owner) != set(range(len(g['ports']))):
            return False
        attachments, by_base = [], {i: [] for i, p in enumerate(profiles) if p['core_ports']}
        for index, a in enumerate(skeleton['attachment_components']):
            check()
            if a['kind'] not in ('circle', 'interval') or not a['word']:
                return False
            ports = [abs(x)-1 for x in a['word']]
            bases, cores = {owner[p] for p in ports}, set()
            if len(bases) != 1:
                return False
            base = next(iter(bases))
            for p in ports:
                port = g['ports'][p]
                dimension, h = port['core_dimension'], port['core_handle']
                if dimension == 0:
                    cores.add(component[h])
                elif dimension == 1:
                    cores.add(component[core['handles1'][h]['ends'][0]])
                else:
                    return False
            if len(cores) != 1:
                return False
            by_base[base].append(index)
            attachments.append((base, next(iter(cores)), a['kind'], index))
        rows = {}
        for h in core['handles2']:
            values = Counter(f['handle'] for f in h['cycle']
                             if f['dimension'] == 1 and f['handle'] not in forest)
            rows[h['id']] = {c: min(2, v) for c, v in values.items()}
        expected_bases = []
        for base in sorted(by_base):
            indices = by_base[base]
            circles = [j for j in indices if skeleton['attachment_components'][j]['kind'] == 'circle']
            if len(circles) > profiles[base]['boundary_components']:
                return False
            if len(circles) < profiles[base]['boundary_components']:
                continue
            if len(circles) != len(indices):
                return False
            counts = Counter()
            for j in circles:
                counts.update(c for c in _walk(g, skeleton['attachment_components'][j]['word'], check)
                              if c not in forest)
            r = len(core['handles2']) + len(expected_bases)
            rows[r] = {c: min(2, value) for c, value in counts.items()}
            expected_bases.append(dict(base_profile=base, relation=r,
                annular_attachments=indices,
                relative_one_handles=1-profiles[base]['euler_characteristic']))
        if not certificate_equal(cert['saturated_bases'], expected_bases):
            return False
        if type(cert['cancellations']) is not list:
            return False
        used = set()
        for pair in cert['cancellations']:
            check()
            if type(pair) is not list or len(pair) != 2:
                return False
            r, c = map(_int, pair)
            if r not in rows or c in used or rows[r].get(c) != 1:
                return False
            if any(other != r and row.get(c, 0) for other, row in rows.items()):
                return False
            used.add(c)
            del rows[r]
        if rows:
            return False

        # Independent connected-component traversal and source Euler census.
        vertices = {('core', c) for c in component}
        vertices.update(('base', b) for b in by_base)
        neighbors = {v: [] for v in vertices}
        for b, c, _, _ in attachments:
            neighbors['base', b].append(('core', c))
            neighbors['core', c].append(('base', b))
        core_chi = Counter(component)
        for h in core['handles1']:
            core_chi[component[h['ends'][0]]] -= 1
        for h in core['handles2']:
            owners = {component[f['handle']] for f in h['cycle'] if f['dimension'] == 0}
            if not owners:
                owners = {component[core['handles1'][f['handle']]['ends'][0]]
                          for f in h['cycle'] if f['dimension'] == 1}
            if len(owners) != 1:
                return False
            core_chi[next(iter(owners))] += 1
        histogram, joined = Counter(), []
        while vertices:
            check()
            start = min(vertices)
            group, todo = set(), [start]
            while todo:
                v = todo.pop()
                if v in group:
                    continue
                group.add(v)
                todo.extend(neighbors[v])
            vertices.difference_update(group)
            cs = sorted(n for kind, n in group if kind == 'core')
            bs = sorted(n for kind, n in group if kind == 'base')
            selected = [(b, c, kind, index) for b, c, kind, index in attachments if b in bs]
            chi = sum(core_chi[n] for n in cs)
            chi += sum(profiles[n]['euler_characteristic'] for n in bs)
            chi -= sum(kind == 'interval' for _, _, kind, _ in selected)
            genus = 1-chi
            if genus < 0:
                return False
            histogram[genus] += 1
            joined.append(dict(core_components=cs, base_profiles=bs,
                attachments=[index for _, _, _, index in selected],
                genus=genus, euler_characteristic=chi))
        isolated = []
        for i, p in enumerate(profiles):
            if not p['core_ports']:
                genus = 1-p['euler_characteristic']
                if genus < 0:
                    return False
                histogram[genus] += p['multiplicity']
                isolated.append(dict(base_profile=i, genus=genus, multiplicity=p['multiplicity']))
        euler = sum((1-g)*n for g, n in histogram.items())
        if euler != (summary['core_euler_characteristic'] + summary['bundle_euler_characteristic']
                     - summary['attachment_euler_characteristic']):
            return False
        expected = dict(histogram=[dict(genus=g, multiplicity=n) for g, n in sorted(histogram.items())],
            components=sum(histogram.values()), ball_components=histogram[0],
            all_balls=all(g == 0 for g in histogram), euler_characteristic=euler,
            joined_components=joined, isolated_bundles=isolated)
        return certificate_equal(cert['census'], expected)
    except (KeyError, IndexError, TypeError, ValueError):
        return False
    except _CallbackFailure as error:
        raise error.args[0]


def verify_normal_cut_saturated(triangulation, coordinates, certificate, *,
                                max_operations=None, check=lambda: None):
    """Replay all six source-orbit proofs before the new finite argument."""
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be a nonnegative integer or None')
    if type(certificate) is not dict or set(certificate) != {'schema', 'parallelity', 'boundary', 'finite'}:
        return False
    if certificate['schema'] != 'normal-cut-saturated-v1':
        return False
    p, b = certificate['parallelity'], certificate['boundary']
    if max_operations is not None:
        try:
            traces = []
            for name in ('vertex_selector', 'boundary_selector', 'polygon_weights', 'fibre_cover'):
                proof = p[name]
                if name.endswith('selector'):
                    proof = proof['weighted_certificate']
                traces.append(proof['orbit_proof']['operations'])
            for name in ('vertex_partition', 'gap_cover'):
                if b[name] is not None:
                    traces.append(b[name]['orbit_proof']['operations'])
            if sum(map(len, traces)) > max_operations:
                return False
        except (KeyError, TypeError):
            return False
    if not verify_normal_cut_parallelity(triangulation, coordinates, p, check=check):
        return False
    if not verify_parallelity_boundary_words(triangulation, coordinates, b, check=check):
        return False
    return replay_saturated_source_census(_decode(p['geometry']), _decode(p['summary']),
                                          _decode(b['skeleton']), certificate['finite'], check=check)
