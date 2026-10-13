"""Finite geometric cancellation kernel for the entire authenticated normal cut.

Bordered I-bundles supply standard boundary disk systems. Every full annulus
adds a real gluing two-handle, and every interface adds a connecting one-handle.
Columns known to start at zero or two and never used as pivots stay implicit.
The enclosing source verifiers, not arbitrary presentations, justify this model.
"""
from collections import Counter

from .core_handlebody import _forest, _occurrences, column_cancellation_plan
from .disk_bundle_absorption import source_core_circle


def bundle_boundary_kernel(g, summary, skeleton, *, check=lambda: None,
                           forest_strategy='canonical'):
    """Return (certificate, census, stats), or None for a conservative refusal."""
    check()
    if forest_strategy not in ('canonical', 'deferred'):
        raise ValueError('forest_strategy must be canonical or deferred')
    core, profiles = g['core'], summary['base_profiles']
    if core['handles3'] or any(p['boundary_components'] <= 0 for p in profiles):
        return None
    tree, component = _forest(core, check)
    if forest_strategy == 'deferred':
        tree = []
    rows = _occurrences(core, tree, check)
    forest = set(tree)
    owner = {port: i for i, p in enumerate(profiles) for port in p['core_ports']}
    port_core = {}
    for port in g['ports']:
        check()
        v = (port['core_handle'] if port['core_dimension'] == 0 else
             core['handles1'][port['core_handle']]['ends'][0])
        port_core[port['id']] = component[v]
    attachments, circles, curves = [], {}, []
    offset = len(core['handles2'])
    for i, a in enumerate(skeleton['attachment_components']):
        check()
        pairs = {(owner[abs(x)-1], port_core[abs(x)-1]) for x in a['word']}
        if len(pairs) != 1 or a['kind'] not in ('interval', 'circle'):
            return None
        base, c = pairs.pop()
        attachments.append(dict(attachment=i, base_profile=base, core_component=c))
        if a['kind'] == 'circle':
            crossings, _ = source_core_circle(g, a['word'], check=check)
            row = {}
            for crossing in crossings:
                h = crossing['handle']
                if h not in forest:
                    row[h] = min(2, row.get(h, 0) + 1)
            rows[offset+i] = row
            circles.setdefault(base, []).append(i)
            curves.append(dict(attachment=i, base_profile=base, crossings=crossings))
    next_column, families = len(core['handles1']), []
    column_node = {h['id']: ('core', component[h['ends'][0]]) for h in core['handles1']
                   if h['id'] not in forest}
    for base, p in enumerate(profiles):
        check()
        if not p['core_ports']:
            continue
        annuli = circles.get(base, [])
        a, b, genus = len(annuli), p['boundary_components'], 1-p['euler_characteristic']
        if p['multiplicity'] != 1 or a > b:
            return None
        dedicated = a if a < b else a-1
        bulk = genus-dedicated
        if bulk < 0:
            return None
        columns = list(range(next_column, next_column+dedicated))
        next_column += dedicated
        for i, h in zip(annuli, columns):
            rows[offset+i][h] = 1
            column_node[h] = ('base', base)
        if a == b:
            for h in columns:
                rows[offset+annuli[-1]][h] = 1
        families.append(dict(base_profile=base, annular_attachments=annuli,
                             boundary_columns=columns, omitted_genus_columns=bulk))
    # Contract a forest of connecting handles only after the source core forest.
    nodes = [('core', c) for c in sorted(set(component))]
    nodes += [('base', i) for i, p in enumerate(profiles) if p['core_ports']]
    parent = {n: n for n in nodes}

    def root(n):
        while parent[n] != n:
            parent[n] = parent[parent[n]]
            n = parent[n]
        return n

    bridges = []
    for edge in attachments:
        check()
        a, b = root(('core', edge['core_component'])), root(('base', edge['base_profile']))
        if a != b:
            parent[max(a,b)] = min(a,b)
            bridges.append(edge['attachment'])
    planned = column_cancellation_plan(rows, check=check)
    if planned['remaining_rows']:
        return None
    removed = {h for _, h in planned['cancellations']}
    if forest_strategy == 'deferred':
        # Every row restricts to a closed walk in the original core graph.
        # A core column leaf is therefore a nonbridge after earlier pivots
        # have been deleted. Base columns are loops and need no exclusion
        # from the core forest. Choose the forest only after discovering
        # the complete schedule; certificates still contract it first.
        tree, surviving_component = _forest(core, check, forbidden=removed)
        if surviving_component != component:
            raise ArithmeticError('deferred boundary pivots changed core connectivity')
        for h in tree:
            del column_node[h]
    # Retained column leaves have no fill on the retained matrix. An omitted
    # column may meet the donor twice; the projected schedule still lifts to
    # the complete geometric model without expanding those columns.
    version = ('bundle-boundary-kernel-v3' if forest_strategy == 'deferred'
               else 'bundle-boundary-kernel-v2')
    proof = dict(schema=version, forest=tree, bridge_forest=bridges,
                 curves=curves, families=families, cancellations=planned['cancellations'])
    groups = {}
    for n in nodes:
        groups.setdefault(root(n), []).append(n)
    histogram, joined = Counter(), []
    for key, vertices in sorted(groups.items()):
        check()
        selected = [i for i, e in enumerate(attachments) if root(('base', e['base_profile'])) == key]
        beta = len(selected)-len(vertices)+1
        finite = sum(h not in removed and root(node) == key for h, node in column_node.items())
        bulk = sum(f['omitted_genus_columns'] for f in families if root(('base', f['base_profile'])) == key)
        genus = finite+bulk+beta
        if beta < 0 or genus < 0:
            return None
        histogram[genus] += 1
        joined.append(dict(core_components=sorted(n[1] for n in vertices if n[0]=='core'),
                           base_profiles=sorted(n[1] for n in vertices if n[0]=='base'),
                           attachments=selected, cycle_rank=beta, genus=genus))
    isolated = []
    for i, p in enumerate(profiles):
        check()
        if not p['core_ports']:
            genus = 1-p['euler_characteristic']
            if genus < 0:
                return None
            histogram[genus] += p['multiplicity']
            isolated.append(dict(base_profile=i, genus=genus, multiplicity=p['multiplicity']))
    euler = sum((1-genus)*n for genus, n in histogram.items())
    if euler != summary['core_euler_characteristic']+summary['bundle_euler_characteristic']-summary['attachment_euler_characteristic']:
        raise ArithmeticError('boundary kernel violates source Euler identity')
    census = dict(histogram=[dict(genus=g, multiplicity=n) for g,n in sorted(histogram.items())],
                  components=sum(histogram.values()), ball_components=histogram[0],
                  all_balls=all(g==0 for g in histogram), euler_characteristic=euler,
                  joined_components=joined, isolated_bundles=isolated, attachments=attachments)
    check()
    return proof, census, dict(planned['stats'], finite_columns=len(column_node),
                              two_handles=len(rows), omitted_genus_columns=sum(f['omitted_genus_columns'] for f in families))
