"""Whole-cut fundamental-group presentations for authenticated disk bases.

The caller authenticates ``geometry``, ``summary``, and the ordered boundary
``skeleton`` using the maintained source checkers.  This module then compiles
the complete graph of spaces, including all disk-bundle circles and intervals.
It performs no group simplification and makes no handlebody decision.

Only bounded source handle/port lists are visited.  Isolated disk bundles are
counted with their binary multiplicities, and their copies are never expanded.
"""


def _forest(core, check):
    """Canonical source graph forest, independently of the raw planner."""
    parent = list(range(len(core['handles0'])))

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    tree = []
    for i, handle in enumerate(core['handles1']):
        check()
        if handle['id'] != i or len(handle['ends']) != 2:
            raise ValueError('noncanonical source one-handle labels')
        a, b = map(root, handle['ends'])
        if a != b:
            parent[max(a, b)] = min(a, b)
            tree.append(i)
    return tree, [root(i) for i in range(len(parent))]


def _original_word(core, handle, tree, check):
    """Read signs from source face flags, including loop one-handles."""
    cycle = handle['cycle']
    if not cycle or len(cycle) % 2:
        raise ValueError('source two-handle is not an alternating closed walk')
    word = []
    for i in range(0, len(cycle), 2):
        check()
        vertex, flag = cycle[i:i + 2]
        following = cycle[(i + 2) % len(cycle)]
        if (vertex['dimension'], flag['dimension'], following['dimension']) != (0, 1, 0):
            raise ValueError('source two-handle has nonalternating flags')
        h = core['handles1'][flag['handle']]
        side = (flag['tetrahedron'], flag['face'])
        source = (h['tetrahedron'], h['face'])
        target = (h['target_tetrahedron'], h['target_face'])
        if side == source and source != target:
            sign = 1
        elif side == target and source != target:
            sign = -1
        else:
            raise ValueError('two-handle flag has no oriented source face')
        endpoints = h['ends'] if sign == 1 else h['ends'][::-1]
        if endpoints != [vertex['handle'], following['handle']]:
            raise ValueError('oriented two-handle walk fails endpoint continuity')
        if h['id'] not in tree:
            word.append(sign * (h['id'] + 1))
    return word, cycle[0]['handle']


def _annular_word(g, attachment, tree, check):
    """Read the actual annular midpoint in authenticated source port charts."""
    core = g['core']
    paths, word = [], []
    for letter in attachment['word']:
        check()
        port = g['ports'][abs(letter) - 1]
        h = port['core_handle']
        if port['core_dimension'] == 0:
            paths.append((h, h))
            continue
        polygon = g['polygons'][port['polygon']]
        edge = port['edge']
        if (port['core_dimension'] != 1 or polygon['kind'] != 'edge_cap'
                or polygon['edges'][edge]['kind'] != 'face_sector'):
            raise ValueError('annulus uses an unsupported one-handle chart')
        handle = core['handles1'][h]
        ends = [(handle['tetrahedron'], handle['face']),
                (handle['target_tetrahedron'], handle['target_face'])]
        flags = [(polygon['vertices'][(edge + j) % len(polygon['vertices'])]['tetrahedron'],
                  polygon['vertices'][(edge + j) % len(polygon['vertices'])]['face'])
                 for j in (0, 1)]
        if flags == ends and ends[0] != ends[1]:
            sign = 1
        elif flags == ends[::-1] and ends[0] != ends[1]:
            sign = -1
        else:
            raise ValueError('annulus face-sector endpoints are inconsistent')
        sign *= 1 if letter > 0 else -1
        endpoints = handle['ends'] if sign == 1 else handle['ends'][::-1]
        paths.append(tuple(endpoints))
        if h not in tree:
            word.append(sign * (h + 1))
    if not paths or any(paths[i][1] != paths[(i + 1) % len(paths)][0]
                        for i in range(len(paths))):
        raise ValueError('annular midpoint is not a closed source path')
    return word, paths[0][0]


def compile_disk_cut_presentation(g, summary, skeleton, *, check=lambda: None):
    """Return a canonical whole-cut group presentation, or ``None``.

    ``None`` means that some base is not an orientable product disk, or an
    incident profile is not a single base copy.  It is never a topological
    negative.  Malformed chart data raises ``ValueError``; the intended caller
    first runs the established independent source and boundary checkers.

    Components have one-based generator labels and a list of relators with
    explicit signed words.  Core forests and interval bridge forests have been
    collapsed.  Three-handles do not affect these group presentations, but do
    contribute to the authenticated global Euler characteristic returned here.
    """
    check()
    core, profiles = g['core'], summary['base_profiles']
    for p in profiles:
        check()
        if (p['euler_characteristic'] != 1 or p['boundary_components'] != 1
                or not p['orientable'] or not p['product']):
            return None
        if p['core_ports'] and p['multiplicity'] != 1:
            return None
    tree_list, component = _forest(core, check)
    tree = set(tree_list)
    port_base, port_component = {}, {}
    for i, p in enumerate(profiles):
        for port in p['core_ports']:
            check()
            if port in port_base:
                raise ValueError('a source port belongs to two bases')
            port_base[port] = i
    for i, port in enumerate(g['ports']):
        check()
        if port['id'] != i or i not in port_base:
            raise ValueError('source port labels or base ownership are invalid')
        d, h = port['core_dimension'], port['core_handle']
        if d == 0:
            vertex = h
        elif d == 1:
            vertex = core['handles1'][h]['ends'][0]
        else:
            raise ValueError('source port has no zero/one-handle owner')
        port_component[i] = component[vertex]

    attachments, by_base, used_ports = [], {}, set()
    for i, a in enumerate(skeleton['attachment_components']):
        check()
        if a['kind'] not in ('interval', 'circle') or not a['word']:
            raise ValueError('invalid source attachment component')
        ports = [abs(x) - 1 for x in a['word']]
        if any(type(x) is not int or x == 0 for x in a['word']):
            raise ValueError('invalid signed source port')
        if len(set(ports)) != len(ports) or used_ports.intersection(ports):
            raise ValueError('source attachment ports are not disjoint')
        used_ports.update(ports)
        owners = {(port_base[p], port_component[p]) for p in ports}
        if len(owners) != 1:
            raise ValueError('connected attachment has inconsistent owners')
        b, c = owners.pop()
        record = dict(id=i, kind=a['kind'], base_profile=b, core_component=c)
        attachments.append(record)
        by_base.setdefault(b, []).append(record)
    if used_ports != set(port_base):
        raise ValueError('ordered attachments do not partition source ports')

    circles, interval_bases = [], []
    for b, p in enumerate(profiles):
        if not p['core_ports']:
            continue
        incident = by_base[b]
        annuli = [a for a in incident if a['kind'] == 'circle']
        if annuli:
            if len(annuli) != 1 or len(incident) != 1:
                raise ValueError('a disk full boundary is used by other attachments')
            circles.append(annuli[0])
        else:
            interval_bases.append(b)

    # Absorbing a disk's complete vertical annulus adds a true two-handle.
    raw_rows = []
    for i, h in enumerate(core['handles2']):
        check()
        if h['id'] != i:
            raise ValueError('noncanonical source two-handle labels')
        word, vertex = _original_word(core, h, tree, check)
        raw_rows.append(dict(id=i, word=word, source_kind='core',
                             core_component=component[vertex]))
    offset = len(core['handles2'])
    for a in circles:
        check()
        word, vertex = _annular_word(g, skeleton['attachment_components'][a['id']],
                                    tree, check)
        if component[vertex] != a['core_component']:
            raise ValueError('annular attaching row has inconsistent component')
        raw_rows.append(dict(id=offset + a['id'], word=word,
                             source_kind='disk_annulus',
                             core_component=component[vertex]))

    # A disk bundle meeting the core along intervals is a ball vertex, with
    # one connecting one-handle per interval.  Nonforest edges are free letters.
    nodes = [('core', c) for c in sorted(set(component))]
    nodes += [('base', b) for b in interval_bases]
    parent = {v: v for v in nodes}

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    bridge_forest, stable = [], []
    next_generator = len(core['handles1']) + 1
    for a in attachments:
        check()
        if a['kind'] != 'interval':
            continue
        x, y = root(('core', a['core_component'])), root(('base', a['base_profile']))
        if x != y:
            parent[max(x, y)] = min(x, y)
            bridge_forest.append(a['id'])
        else:
            stable.append((a, next_generator))
            next_generator += 1
    groups = {}
    for node in nodes:
        groups.setdefault(root(node), []).append(node)
    ordered = sorted(groups.values(), key=lambda vs: min(v[1] for v in vs if v[0] == 'core'))
    parts, part_by_core = [], {}
    for nodes_here in ordered:
        cores = sorted(v[1] for v in nodes_here if v[0] == 'core')
        bases = sorted(v[1] for v in nodes_here if v[0] == 'base')
        label = min(cores)
        part = dict(id=label, core_components=cores, interval_bases=bases,
                    annular_bases=[], generators=[], relators=[],
                    attachment_cycle_rank=0)
        parts.append(part)
        for c in cores:
            part_by_core[c] = part
    for h in core['handles1']:
        check()
        if h['id'] not in tree:
            part_by_core[component[h['ends'][0]]]['generators'].append(h['id'] + 1)
    for a, generator in stable:
        part = part_by_core[a['core_component']]
        part['generators'].append(generator)
        part['attachment_cycle_rank'] += 1
    for a in circles:
        part_by_core[a['core_component']]['annular_bases'].append(a['base_profile'])
    for r in raw_rows:
        c = r.pop('core_component')
        part_by_core[c]['relators'].append(r)
    for p in parts:
        p['annular_bases'].sort()
        p['relators'].sort(key=lambda r: r['id'])
        alphabet = set(p['generators'])
        if any(abs(x) not in alphabet for r in p['relators'] for x in r['word']):
            raise ValueError('relator crosses whole-cut connected components')
    isolated = sum(p['multiplicity'] for p in profiles if not p['core_ports'])
    euler = (summary['core_euler_characteristic'] + summary['bundle_euler_characteristic']
             - summary['attachment_euler_characteristic'])
    active_generators = sum(len(p['generators']) for p in parts)
    active_relators = sum(len(p['relators']) for p in parts)
    handle_euler = (len(parts) + isolated - active_generators + active_relators
                    - len(core['handles3']))
    if handle_euler != euler:
        raise ValueError('compiled whole-cut handles violate source Euler identity')
    check()
    return dict(schema='source-disk-cut-presentation-v1', components=parts,
                isolated_ball_count=isolated, core_forest=tree_list,
                bridge_forest=bridge_forest, source_euler_characteristic=euler,
                stats=dict(core_zero_handles=len(core['handles0']),
                           core_one_handles=len(core['handles1']),
                           core_two_handles=len(core['handles2']),
                           core_three_handles=len(core['handles3']),
                           ports=len(g['ports']), disk_profiles=len(profiles),
                           annular_relators=len(circles),
                           interval_attachments=sum(a['kind'] == 'interval' for a in attachments),
                           stable_generators=len(stable),
                           generators=active_generators,
                           relators=active_relators,
                           word_length=sum(len(r['word']) for p in parts for r in p['relators'])))
