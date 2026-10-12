"""Independent replay of source-bound whole-cut disk-base presentations.

This checker imports neither the presentation compiler nor any cancellation
producer.  It authenticates supplied forests by separate graph traversals,
reads every relator from the source face and polygon charts, and reconstructs
the whole-cut graph of spaces.  Native enclosing checkers must first authenticate
the triangulation-derived geometry, summary and ordered boundary skeleton.
"""

from .integer_codec import certificate_equal, encoded_integer


def _components(vertices, edges, check):
    adjacent = {v: [] for v in vertices}
    for u, v in edges:
        check()
        if u not in adjacent or v not in adjacent:
            raise ValueError('edge endpoint is outside the graph')
        adjacent[u].append(v)
        adjacent[v].append(u)
    unseen, groups, owner = set(vertices), [], {}
    while unseen:
        seed = min(unseen)
        todo, reached = [seed], set()
        while todo:
            check()
            u = todo.pop()
            if u in reached:
                continue
            reached.add(u)
            todo.extend(v for v in adjacent[u] if v not in reached)
        unseen.difference_update(reached)
        group = sorted(reached)
        groups.append(group)
        for v in group:
            owner[v] = group[0]
    return groups, owner


def _spanning_forest(vertices, edges, chosen, check):
    """Check forestness by edge counts and independent component traversals."""
    if type(chosen) is not list:
        raise ValueError('forest must be a list')
    labels = [encoded_integer(x) for x in chosen]
    if labels != sorted(set(labels)) or any(i not in edges for i in labels):
        raise ValueError('forest has repeated or unknown edge labels')
    groups, owner = _components(vertices, edges.values(), check)
    forest_groups, forest_owner = _components(vertices, [edges[i] for i in labels], check)
    if groups != forest_groups or len(labels) != len(vertices) - len(groups):
        raise ValueError('supplied edges do not form a spanning forest')
    if owner != forest_owner:
        raise ValueError('forest component partition is inconsistent')
    return labels, groups, owner


def _replay(g, summary, skeleton, proof, check):
    if type(proof) is not dict or proof.get('schema') != 'source-disk-cut-presentation-v1':
        return None
    core, profiles = g['core'], summary['base_profiles']
    for p in profiles:
        check()
        if (p['euler_characteristic'] != 1 or p['boundary_components'] != 1
                or p['orientable'] is not True or p['product'] is not True
                or (p['core_ports'] and p['multiplicity'] != 1)):
            return None
    zeros = list(range(len(core['handles0'])))
    edge_table = {}
    oriented_faces = {}
    for i, h in enumerate(core['handles1']):
        check()
        if h['id'] != i or len(h['ends']) != 2:
            raise ValueError('source one-handle labels are not canonical')
        u, v = h['ends']
        edge_table[i] = (u, v)
        forward = (h['tetrahedron'], h['face'])
        backward = (h['target_tetrahedron'], h['target_face'])
        if forward == backward:
            raise ValueError('source one-handle has only one face flag')
        oriented_faces[i, forward] = (u, v, 1)
        oriented_faces[i, backward] = (v, u, -1)
    forest, core_groups, core_owner = _spanning_forest(zeros, edge_table,
                                                       proof['core_forest'], check)
    forest_set = set(forest)

    # Build the positive direction of each port directly from its own chart.
    port_table, base_ports = {}, {}
    for b, p in enumerate(profiles):
        check()
        for port in p['core_ports']:
            if port in base_ports:
                raise ValueError('base profiles repeat a core port')
            base_ports[port] = b
    for i, p in enumerate(g['ports']):
        check()
        if p['id'] != i or i not in base_ports:
            raise ValueError('source core port partition is invalid')
        d, h = p['core_dimension'], p['core_handle']
        if d == 0:
            begin, end, letter = h, h, None
        elif d == 1:
            polygon = g['polygons'][p['polygon']]
            edge = p['edge']
            if (polygon['kind'] != 'edge_cap'
                    or polygon['edges'][edge]['kind'] != 'face_sector'):
                raise ValueError('source port is not a one-handle face-sector chart')
            v0 = polygon['vertices'][edge]
            v1 = polygon['vertices'][(edge + 1) % len(polygon['vertices'])]
            begin, end, direction = oriented_faces[h, (v0['tetrahedron'], v0['face'])]
            other_begin, other_end, other_direction = oriented_faces[h, (v1['tetrahedron'], v1['face'])]
            if (other_begin, other_end, other_direction) != (end, begin, -direction):
                raise ValueError('a port does not cross opposite one-handle faces')
            letter = direction * (h + 1)
        else:
            raise ValueError('core port dimension is invalid')
        if core_owner[begin] != core_owner[end]:
            raise ValueError('source port joins different core graph components')
        port_table[i] = (base_ports[i], core_owner[begin], begin, end, letter)
    if set(base_ports) != set(port_table):
        raise ValueError('base profile includes an absent port')

    used, attachments, incident = set(), [], {}
    annular_rows = []
    offset = len(core['handles2'])
    for i, a in enumerate(skeleton['attachment_components']):
        check()
        if a['kind'] not in ('circle', 'interval') or type(a['word']) is not list or not a['word']:
            raise ValueError('invalid boundary attachment type')
        pairs, steps, word = set(), [], []
        for signed in a['word']:
            check()
            if type(signed) is not int or signed == 0:
                raise ValueError('invalid signed port')
            port = abs(signed) - 1
            if port in used:
                raise ValueError('a port is used by several attachment positions')
            used.add(port)
            b, c, begin, end, letter = port_table[port]
            pairs.add((b, c))
            if signed < 0:
                begin, end = end, begin
                if letter is not None:
                    letter = -letter
            steps.append((begin, end))
            if letter is not None and abs(letter) - 1 not in forest_set:
                word.append(letter)
        if len(pairs) != 1:
            raise ValueError('attachment has inconsistent base/core owners')
        b, c = pairs.pop()
        record = dict(id=i, kind=a['kind'], base=b, core=c)
        attachments.append(record)
        incident.setdefault(b, []).append(record)
        if a['kind'] == 'circle':
            if any(steps[j][1] != steps[(j + 1) % len(steps)][0]
                   for j in range(len(steps))):
                raise ValueError('annular source path is not closed')
            annular_rows.append((c, dict(id=offset + i, word=word,
                                         source_kind='disk_annulus')))
    if used != set(port_table):
        raise ValueError('ordered boundary words omit a source port')
    interval_bases, annular_bases = [], []
    for b, p in enumerate(profiles):
        check()
        if not p['core_ports']:
            continue
        attached = incident[b]
        n_circles = sum(a['kind'] == 'circle' for a in attached)
        if n_circles:
            if len(attached) != 1:
                raise ValueError('full disk boundary shares another attachment')
            annular_bases.append((b, attached[0]['core']))
        else:
            interval_bases.append(b)

    # Whole-cut components follow the disk-intersection graph, independently
    # of any cancellation or claimed component labels in the presentation.
    nodes = [('core', vs[0]) for vs in core_groups]
    nodes += [('base', b) for b in interval_bases]
    interval_edges = {a['id']: (('core', a['core']), ('base', a['base']))
                      for a in attachments if a['kind'] == 'interval'}
    bridges, joined_groups, joined_owner = _spanning_forest(nodes, interval_edges,
                                                           proof['bridge_forest'], check)
    by_core, components = {}, []
    for vs in joined_groups:
        cores = sorted(v[1] for v in vs if v[0] == 'core')
        if not cores:
            raise ValueError('ported disk component has no core vertex')
        p = dict(id=cores[0], core_components=cores,
                 interval_bases=sorted(v[1] for v in vs if v[0] == 'base'),
                 annular_bases=[], generators=[], relators=[],
                 attachment_cycle_rank=0)
        components.append(p)
        for c in cores:
            by_core[c] = p
    components.sort(key=lambda p: p['id'])
    for i, (u, v) in edge_table.items():
        check()
        if i not in forest_set:
            by_core[core_owner[u]]['generators'].append(i + 1)
    next_generator = len(edge_table) + 1
    for a in attachments:
        check()
        if a['kind'] == 'interval' and a['id'] not in bridges:
            p = by_core[a['core']]
            p['generators'].append(next_generator)
            p['attachment_cycle_rank'] += 1
            next_generator += 1
    for b, c in annular_bases:
        by_core[c]['annular_bases'].append(b)

    # Original attaching loops: signs come from face flags, never exponent sums
    # of the unsigned cancellation matrix or a simplified group presentation.
    for i, h in enumerate(core['handles2']):
        check()
        walk = h['cycle']
        if h['id'] != i or not walk or len(walk) % 2:
            raise ValueError('source two-handle walk has invalid shape')
        word = []
        component = None
        for j in range(0, len(walk), 2):
            check()
            zero, one, successor = walk[j], walk[j + 1], walk[(j + 2) % len(walk)]
            if (zero['dimension'], one['dimension'], successor['dimension']) != (0, 1, 0):
                raise ValueError('source attaching loop is not alternating')
            handle = one['handle']
            begin, end, direction = oriented_faces[handle, (one['tetrahedron'], one['face'])]
            if zero['handle'] != begin or successor['handle'] != end:
                raise ValueError('source attaching loop has incorrect endpoint flags')
            here = core_owner[begin]
            if component is not None and component != here:
                raise ValueError('source attaching loop changes graph components')
            component = here
            if handle not in forest_set:
                word.append(direction * (handle + 1))
        by_core[component]['relators'].append(dict(id=i, word=word, source_kind='core'))
    for c, row in annular_rows:
        by_core[c]['relators'].append(row)
    for p in components:
        p['relators'].sort(key=lambda r: r['id'])
        p['annular_bases'].sort()

    isolated = sum(p['multiplicity'] for p in profiles if not p['core_ports'])
    euler = (summary['core_euler_characteristic'] + summary['bundle_euler_characteristic']
             - summary['attachment_euler_characteristic'])
    generators = sum(len(p['generators']) for p in components)
    relators = sum(len(p['relators']) for p in components)
    if (len(components) + isolated - generators + relators
            - len(core['handles3'])) != euler:
        raise ValueError('source Euler characteristic disagrees with the compiled handles')
    expected = dict(schema='source-disk-cut-presentation-v1', components=components,
                    isolated_ball_count=isolated, core_forest=forest,
                    bridge_forest=bridges, source_euler_characteristic=euler,
                    stats=dict(core_zero_handles=len(core['handles0']),
                               core_one_handles=len(core['handles1']),
                               core_two_handles=len(core['handles2']),
                               core_three_handles=len(core['handles3']),
                               ports=len(g['ports']), disk_profiles=len(profiles),
                               annular_relators=len(annular_rows),
                               interval_attachments=len(interval_edges),
                               stable_generators=len(interval_edges) - len(bridges),
                               generators=generators, relators=relators,
                               word_length=sum(len(r['word']) for p in components for r in p['relators'])))
    return expected if certificate_equal(proof, expected) else None


def verify_disk_cut_presentation(g, summary, skeleton, presentation, *, check=lambda: None):
    """Check the whole presentation against already authenticated source data."""
    check()
    callback_failed = False

    def callback():
        nonlocal callback_failed
        try:
            check()
        except BaseException:
            callback_failed = True
            raise

    try:
        return _replay(g, summary, skeleton, presentation, callback) is not None
    except (KeyError, IndexError, TypeError, ValueError):
        if callback_failed:
            raise
        return False
