"""Independent source reconstruction and dense replay for the whole-cut kernel.

No producer, forest helper, census helper, or cancellation planner is imported.
Inputs must first pass the source parallelity and marked-boundary verifiers.
"""
from collections import Counter

from .disk_bundle_absorption_verify import reconstruct_core_circle
from .integer_codec import certificate_equal, encoded_integer


def replay_bundle_boundary_kernel(g, summary, skeleton, certificate, *, check=lambda: None):
    """Return the independently recounted census, or None on failed replay."""
    check()
    required = {'schema', 'forest', 'bridge_forest', 'curves', 'families', 'cancellations'}
    if type(certificate) is not dict or set(certificate) != required:
        return None
    if certificate['schema'] != 'bundle-boundary-kernel-v1':
        return None
    core, bases = g['core'], summary['base_profiles']
    if core['handles3'] or any(p['boundary_components'] <= 0 for p in bases):
        return None
    if not core['handles0']:
        return None
    # Independent set-merging constructs the canonical source forest.
    component = list(range(len(core['handles0'])))
    tree = []
    for h in core['handles1']:
        check()
        a, b = (component[v] for v in h['ends'])
        if a != b:
            component = [min(a,b) if x in (a,b) else x for x in component]
            tree.append(h['id'])
    on_tree = set(tree)
    columns = {h['id']: ('core', component[h['ends'][0]]) for h in core['handles1']
               if h['id'] not in on_tree}
    raw_rows = {}
    for h in core['handles2']:
        check()
        counts = Counter(f['handle'] for f in h['cycle'] if f['dimension']==1 and f['handle'] not in on_tree)
        raw_rows[h['id']] = {c: min(2,n) for c,n in counts.items()}
    port_base = {port: i for i, p in enumerate(bases) for port in p['core_ports']}
    port_owner = {}
    for p in g['ports']:
        check()
        if p['core_dimension']==0:
            v = p['core_handle']
        elif p['core_dimension']==1:
            v = core['handles1'][p['core_handle']]['ends'][0]
        else:
            return None
        port_owner[p['id']] = component[v]
    edges, curves, base_annuli = [], [], {}
    offset = len(core['handles2'])
    for index, a in enumerate(skeleton['attachment_components']):
        check()
        owners = {(port_base[abs(x)-1], port_owner[abs(x)-1]) for x in a['word']}
        if len(owners)!=1 or a['kind'] not in ('circle','interval'):
            return None
        base, c = next(iter(owners))
        edges.append(dict(attachment=index, base_profile=base, core_component=c))
        if a['kind']=='circle':
            traced = reconstruct_core_circle(g, a, check=check)
            if traced is None:
                return None
            crossings, _ = traced
            counts = Counter(x['handle'] for x in crossings if x['handle'] not in on_tree)
            raw_rows[offset+index] = {h: min(2,n) for h,n in counts.items()}
            base_annuli.setdefault(base,[]).append(index)
            curves.append(dict(attachment=index, base_profile=base, crossings=crossings))
    families, next_column = [], len(core['handles1'])
    for i, base in enumerate(bases):
        check()
        if not base['core_ports']:
            continue
        annuli = base_annuli.get(i,[])
        number, boundary = len(annuli), base['boundary_components']
        if base['multiplicity'] != 1 or number > boundary:
            return None
        retained = min(number, boundary-1)
        implicit = 1-base['euler_characteristic']-retained
        if implicit < 0:
            return None
        selected = list(range(next_column,next_column+retained))
        next_column += retained
        for j, h in enumerate(selected):
            columns[h] = ('base',i)
            raw_rows[offset+annuli[j]][h] = 1
            if number==boundary:
                raw_rows[offset+annuli[-1]][h] = 1
        families.append(dict(base_profile=i, annular_attachments=annuli,
                             boundary_columns=selected, omitted_genus_columns=implicit))
    # Reconstruct the connecting forest with explicit partitions, and retain
    # adjacency separately for the independent component census below.
    nodes = [('core',c) for c in sorted(set(component))]
    nodes += [('base',i) for i,b in enumerate(bases) if b['core_ports']]
    parts = [{n} for n in nodes]
    adjacent = {n: [] for n in nodes}
    bridges = []
    for e in edges:
        check()
        a, b = ('core',e['core_component']), ('base',e['base_profile'])
        adjacent[a].append(b)
        adjacent[b].append(a)
        left = next(p for p in parts if a in p)
        right = next(p for p in parts if b in p)
        if left is not right:
            left.update(right)
            parts.remove(right)
            bridges.append(e['attachment'])
    moves = certificate['cancellations']
    if type(moves) is not list or len(moves) != len(raw_rows):
        return None
    expected = dict(schema='bundle-boundary-kernel-v1', forest=tree, bridge_forest=bridges,
                    curves=curves, families=families, cancellations=moves)
    if not certificate_equal(certificate, expected):
        return None
    # The retained columns alone determine retained counts under positive
    # pivots. Implicit columns start in {0,2} and can never be chosen.
    labels = sorted(raw_rows)
    position = {r:i for i,r in enumerate(labels)}
    matrix = [[raw_rows[r].get(c,0) for c in range(next_column)] for r in labels]
    live_rows, live_columns = set(labels), set(columns)
    for move in moves:
        check()
        if type(move) is not list or len(move)!=2:
            return None
        try:
            r,c = map(encoded_integer,move)
        except ValueError:
            return None
        if r not in live_rows or c not in live_columns or matrix[position[r]][c]!=1:
            return None
        live_rows.remove(r)
        live_columns.remove(c)
        donor = matrix[position[r]]
        for other in live_rows:
            check()
            row = matrix[position[other]]
            coefficient = row[c]
            for h in live_columns:
                row[h] = min(2,row[h]+coefficient*donor[h])
            row[c] = 0
    if live_rows:
        return None
    unseen, joined, histogram = set(nodes), [], Counter()
    while unseen:
        check()
        pending, group = [min(unseen)], set()
        while pending:
            n = pending.pop()
            if n not in group:
                group.add(n)
                pending.extend(adjacent[n])
        unseen.difference_update(group)
        selected = [i for i,e in enumerate(edges) if ('base',e['base_profile']) in group]
        beta = len(selected)-len(group)+1
        # Independently count original handles minus *all* two-handles,
        # instead of copying the producer's surviving-column census.
        initial = sum(n in group for n in columns.values())
        initial += sum(f['omitted_genus_columns'] for f in families if ('base',f['base_profile']) in group)
        real = sum(('core',component[h['cycle'][0]['handle']]) in group for h in core['handles2'])
        annular = sum(('base',c['base_profile']) in group for c in curves)
        genus = initial+beta-real-annular
        # A successful local pivot must also preserve component ownership.
        survived = sum(columns[h] in group for h in live_columns)
        survived += sum(f['omitted_genus_columns'] for f in families if ('base',f['base_profile']) in group)
        if beta<0 or genus<0 or genus!=survived+beta:
            return None
        histogram[genus] += 1
        joined.append(dict(core_components=sorted(n[1] for n in group if n[0]=='core'),
                           base_profiles=sorted(n[1] for n in group if n[0]=='base'),
                           attachments=selected, cycle_rank=beta, genus=genus))
    isolated = []
    for i,p in enumerate(bases):
        check()
        if not p['core_ports']:
            genus = 1-p['euler_characteristic']
            if genus<0:
                return None
            histogram[genus] += p['multiplicity']
            isolated.append(dict(base_profile=i,genus=genus,multiplicity=p['multiplicity']))
    euler = sum(n*(1-g) for g,n in histogram.items())
    if euler != summary['core_euler_characteristic']+summary['bundle_euler_characteristic']-summary['attachment_euler_characteristic']:
        return None
    check()
    return dict(histogram=[dict(genus=g,multiplicity=n) for g,n in sorted(histogram.items())],
                components=sum(histogram.values()), ball_components=histogram[0],
                all_balls=all(g==0 for g in histogram),euler_characteristic=euler,
                joined_components=joined,isolated_bundles=isolated,attachments=edges)
