"""Opt-in source census with saturated bundle relations and core cancellations.

A saturated bordered interval bundle has a relative decomposition with
1-chi(base) one-handles and one two-handle.  The latter crosses each inherited
core cocore as often as the full annular boundary words do in total.  New
bundle handles are never enumerated or selected as pivots.  Column-leaf
cancellation removes all old and new two-handles when this sufficient
geometric criterion succeeds.  Unsaturated bundles attach afterwards.

This is an unmarked whole-cut topology certificate, not a knot verdict or a
boundary-pattern transport certificate.  Source contracts are authenticated
by the parallelity and boundary-word proofs in the enclosing certificate.
"""

from collections import Counter

from .core_handlebody import column_cancellation_plan
from .normal_parallelity import normal_cut_parallelity
from .parallelity_boundary_words import normal_parallelity_boundary_words


def _forest(core, check):
    parent = list(range(len(core['handles0'])))

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    selected = []
    for h in core['handles1']:
        check()
        a, b = (root(v) for v in h['ends'])
        if a != b:
            parent[max(a, b)] = min(a, b)
            selected.append(h['id'])
    return selected, [root(v) for v in range(len(parent))]


def _circle_crossings(g, word, check):
    """Authenticate the midpoint core path at each face-sector port."""
    paths, crossings = [], []
    for letter in word:
        check()
        port = g['ports'][abs(letter) - 1]
        number = port['core_handle']
        if port['core_dimension'] == 0:
            paths.append((number, number))
            continue
        if port['core_dimension'] != 1:
            raise ArithmeticError('invalid annular core port dimension')
        poly, slot = g['polygons'][port['polygon']], port['edge']
        if poly['kind'] != 'edge_cap' or poly['edges'][slot]['kind'] != 'face_sector':
            raise ArithmeticError('annular port is not a face sector')
        handle = g['core']['handles1'][number]
        ends = [(handle['tetrahedron'], handle['face']),
                (handle['target_tetrahedron'], handle['target_face'])]
        flags = [(poly['vertices'][(slot + j) % len(poly['vertices'])]['tetrahedron'],
                  poly['vertices'][(slot + j) % len(poly['vertices'])]['face'])
                 for j in (0, 1)]
        if flags == ends:
            sign = 1
        elif flags == ends[::-1]:
            sign = -1
        else:
            raise ArithmeticError('annular endpoint charts disagree')
        sign *= 1 if letter > 0 else -1
        paths.append(tuple(handle['ends'][::sign]))
        crossings.append(number)
    if not paths or any(paths[j][1] != paths[(j + 1) % len(paths)][0]
                        for j in range(len(paths))):
        raise ArithmeticError('annular midpoint word is not a closed core path')
    return crossings


def _source_rows(g, summary, skeleton, forest, components, check):
    profiles, core = summary['base_profiles'], g['core']
    if core['handles3']:
        return None, 'core_has_three_handles'
    if any(p['boundary_components'] <= 0 for p in profiles):
        return None, 'closed_bundle_base'
    by_port = {port: i for i, p in enumerate(profiles) for port in p['core_ports']}
    attached = {i: [] for i, p in enumerate(profiles) if p['core_ports']}
    edges = []
    for j, a in enumerate(skeleton['attachment_components']):
        check()
        ports = [abs(letter) - 1 for letter in a['word']]
        if not ports or a['kind'] not in ('circle', 'interval'):
            raise ArithmeticError('invalid attachment component')
        bases = {by_port[p] for p in ports}
        if len(bases) != 1:
            raise ArithmeticError('attachment has inconsistent base owners')
        base = bases.pop()
        owners = set()
        for p in ports:
            port = g['ports'][p]
            if port['core_dimension'] == 0:
                v = port['core_handle']
            elif port['core_dimension'] == 1:
                v = core['handles1'][port['core_handle']]['ends'][0]
            else:
                raise ArithmeticError('invalid core-facing port')
            owners.add(components[v])
        if len(owners) != 1:
            raise ArithmeticError('attachment has inconsistent core owners')
        attached[base].append(j)
        edges.append(dict(attachment=j, base_profile=base,
                          core_component=owners.pop(), kind=a['kind']))
    saturated = []
    for base, indices in sorted(attached.items()):
        check()
        p = profiles[base]
        if p['multiplicity'] != 1:
            raise ArithmeticError('ported base has non-unit multiplicity')
        circles = [j for j in indices
                   if skeleton['attachment_components'][j]['kind'] == 'circle']
        if len(circles) > p['boundary_components']:
            raise ArithmeticError('too many full base boundary components')
        if len(circles) == p['boundary_components']:
            if len(circles) != len(indices):
                raise ArithmeticError('saturated base has a proper interval')
            saturated.append(base)
    removed = set(forest)
    rows = {}
    for h in core['handles2']:
        row = Counter()
        for flag in h['cycle']:
            if flag['dimension'] == 1 and flag['handle'] not in removed:
                row[flag['handle']] += 1
        rows[h['id']] = {c: min(2, n) for c, n in row.items()}
    records = []
    for base in saturated:
        row = Counter()
        for j in attached[base]:
            a = skeleton['attachment_components'][j]
            row.update(c for c in _circle_crossings(g, a['word'], check)
                       if c not in removed)
        number = len(core['handles2']) + len(records)
        rows[number] = {c: min(2, n) for c, n in row.items()}
        records.append(dict(base_profile=base, relation=number,
                            annular_attachments=attached[base],
                            relative_one_handles=1-profiles[base]['euler_characteristic']))
    return dict(rows=rows, saturated=records, attachments=edges), None


def _census(g, summary, source, components, check):
    core, profiles = g['core'], summary['base_profiles']
    core_chi = Counter(components)
    for h in core['handles1']:
        core_chi[components[h['ends'][0]]] -= 1
    for h in core['handles2']:
        owners = {components[f['handle']] for f in h['cycle'] if f['dimension'] == 0}
        if not owners:
            owners = {components[core['handles1'][f['handle']]['ends'][0]]
                      for f in h['cycle'] if f['dimension'] == 1}
        if len(owners) != 1:
            raise ArithmeticError('core two-handle owner is not unique')
        core_chi[owners.pop()] += 1
    nodes = [('core', i) for i in sorted(set(components))]
    nodes += [('base', i) for i, p in enumerate(profiles) if p['core_ports']]
    parent = {n: n for n in nodes}

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for e in source['attachments']:
        a, b = root(('base', e['base_profile'])), root(('core', e['core_component']))
        if a != b:
            parent[max(a, b)] = min(a, b)
    groups = {}
    for n in nodes:
        groups.setdefault(root(n), []).append(n)
    grouped_edges = {key: [] for key in groups}
    for edge in source['attachments']:
        grouped_edges[root(('base', edge['base_profile']))].append(edge)
    histogram, joined = Counter(), []
    for key, group in sorted(groups.items()):
        check()
        selected = grouped_edges[key]
        chi = sum(core_chi[n] for kind, n in group if kind == 'core')
        chi += sum(profiles[n]['euler_characteristic'] for kind, n in group if kind == 'base')
        chi -= sum(e['kind'] == 'interval' for e in selected)
        genus = 1 - chi
        if genus < 0:
            raise ArithmeticError('successful cancellation has negative genus')
        histogram[genus] += 1
        joined.append(dict(core_components=[n for kind, n in group if kind == 'core'],
                           base_profiles=[n for kind, n in group if kind == 'base'],
                           attachments=[e['attachment'] for e in selected],
                           genus=genus, euler_characteristic=chi))
    isolated = []
    for i, p in enumerate(profiles):
        if not p['core_ports']:
            genus = 1 - p['euler_characteristic']
            histogram[genus] += p['multiplicity']
            isolated.append(dict(base_profile=i, genus=genus,
                                 multiplicity=p['multiplicity']))
    euler = sum((1-g)*n for g, n in histogram.items())
    expected = (summary['core_euler_characteristic'] + summary['bundle_euler_characteristic']
                - summary['attachment_euler_characteristic'])
    if euler != expected:
        raise ArithmeticError('saturated census violates source Euler identity')
    return dict(histogram=[dict(genus=g, multiplicity=n) for g, n in sorted(histogram.items())],
                components=sum(histogram.values()), ball_components=histogram[0],
                all_balls=all(g == 0 for g in histogram), euler_characteristic=euler,
                joined_components=joined, isolated_bundles=isolated)


def saturated_source_census(g, summary, skeleton, *, check=lambda: None):
    """Finite operator; its inputs need the enclosing source authentications."""
    check()
    forest, components = _forest(g['core'], check)
    source, reason = _source_rows(g, summary, skeleton, forest, components, check)
    if source is None:
        return dict(status='INCONCLUSIVE', reason=reason)
    plan = column_cancellation_plan(source['rows'], check=check)
    schedule, remaining = plan['cancellations'], plan['remaining_rows']
    stats = dict(rows=len(source['rows']), incidence=sum(map(len, source['rows'].values())),
                 saturated_bases=len(source['saturated']),
                 incidence_visits=plan['stats']['incidence_visits'])
    if remaining:
        return dict(status='INCONCLUSIVE', reason='saturated_raw_cancellation_stalled',
                    remaining_rows=remaining, stats=stats)
    census = _census(g, summary, source, components, check)
    proof = dict(schema='saturated-source-census-v1', forest=forest,
                 saturated_bases=source['saturated'], cancellations=schedule, census=census)
    return dict(status='COMPLETE', census=census, certificate=proof, stats=stats)


def normal_cut_saturated(triangulation, coordinates, *, max_cycles=None,
                         record_certificate=False, check=lambda: None):
    """Classify a supplied cut, retaining INCONCLUSIVE on unsupported inputs."""
    check()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    p = normal_cut_parallelity(triangulation, coordinates, max_cycles=max_cycles,
                              record_certificate=record_certificate, check=check)
    result = dict(status='INCONCLUSIVE', trust='source cut census; no standalone knot verdict',
                  stats=dict(parallelity=p['stats']))
    if p['status'] != 'COMPLETE':
        result['reason'] = 'parallelity_budget_exhausted'
        return result
    if p['geometry']['core']['handles3']:
        result['reason'] = 'core_has_three_handles'
        return result
    remaining = max_cycles
    if remaining is not None:
        remaining -= sum(s['orbit_cycles'] for s in p['stats'].values())
    b = normal_parallelity_boundary_words(triangulation, coordinates, max_cycles=remaining,
                                          record_certificate=record_certificate, check=check)
    result['stats']['boundary'] = b['stats']
    if b['status'] != 'COMPLETE':
        result['reason'] = 'boundary_budget_exhausted'
        return result
    finite = saturated_source_census(p['geometry'], p['summary'], b['skeleton'], check=check)
    result['stats']['finite'] = finite.get('stats', {})
    if finite['status'] != 'COMPLETE':
        result['reason'] = finite['reason']
        if 'remaining_rows' in finite:
            result['remaining_rows'] = finite['remaining_rows']
        return result
    result.update(status='COMPLETE', census=finite['census'])
    if record_certificate:
        result['certificate'] = dict(schema='normal-cut-saturated-v1',
            parallelity=p['certificate'], boundary=b['certificate'], finite=finite['certificate'])
    check()
    return result
