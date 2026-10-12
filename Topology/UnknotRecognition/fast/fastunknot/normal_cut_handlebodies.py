"""Source-certified handlebody census with disk-bundle annulus absorption.

This conservative terminal operator combines the complete source parallelity
decomposition, ordered core attachments, and geometric core cancellations.
It never infers a ball from homology or a sphere boundary alone.  Nondisk annular
attachments, closed bundle bases, or stalled core cancellations are unresolved.
"""

from collections import Counter

from .core_handlebody import core_handlebody_certificate
from .disk_bundle_absorption import absorb_disk_bundles
from .normal_parallelity import normal_cut_parallelity
from .parallelity_boundary_words import normal_parallelity_boundary_words


def _census(geometry, summary, skeleton, components, check, absorbed=frozenset()):
    profiles = summary['base_profiles']
    if any(p['boundary_components'] == 0 for p in profiles):
        return None, 'closed_bundle_base'
    owner = {v: c['id'] for c in components for v in c['zero_handles']}
    port_base = {p: i for i, profile in enumerate(profiles)
                 for p in profile['core_ports']}
    port_core = {}
    for port in geometry['ports']:
        check()
        dimension, handle = port['core_dimension'], port['core_handle']
        if dimension == 0:
            vertex = handle
        elif dimension == 1:
            vertex = geometry['core']['handles1'][handle]['ends'][0]
        else:
            raise ArithmeticError('invalid core-facing port owner')
        port_core[port['id']] = owner[vertex]
    nodes = [('core', c['id']) for c in components]
    nodes += [('base', i) for i, p in enumerate(profiles) if p['core_ports'] and i not in absorbed]
    parent = {v: v for v in nodes}
    genera = {('core', c['id']): c['genus'] for c in components}
    genera.update({('base', i): 1 - p['euler_characteristic']
                   for i, p in enumerate(profiles) if p['core_ports'] and i not in absorbed})

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    edges = []
    for i, attachment in enumerate(skeleton['attachment_components']):
        check()
        ports = [abs(p) - 1 for p in attachment['word']]
        if attachment['kind'] == 'circle' and port_base[ports[0]] in absorbed:
            continue
        bases = {port_base[p] for p in ports}
        cores = {port_core[p] for p in ports}
        if attachment['kind'] != 'interval' or len(bases) != 1 or len(cores) != 1:
            raise ArithmeticError('one connected disk attachment has inconsistent owners')
        b, c = next(iter(bases)), next(iter(cores))
        left, right = ('base', b), ('core', c)
        a, z = root(left), root(right)
        if a != z:
            parent[max(a, z)] = min(a, z)
        edges.append(dict(attachment=i, base_profile=b, core_component=c))
    groups = {}
    for v in nodes:
        groups.setdefault(root(v), []).append(v)
    histogram = Counter()
    joined = []
    for key, vertices in sorted(groups.items()):
        check()
        selected = [i for i, e in enumerate(edges)
                    if root(('base', e['base_profile'])) == key]
        cycle_rank = len(selected) - len(vertices) + 1
        genus = sum(genera[v] for v in vertices) + cycle_rank
        if genus < 0 or cycle_rank < 0:
            raise ArithmeticError('invalid disk-gluing graph genus')
        histogram[genus] += 1
        joined.append(dict(core_components=sorted(v[1] for v in vertices if v[0] == 'core'),
                           base_profiles=sorted(v[1] for v in vertices if v[0] == 'base'),
                           attachments=selected, cycle_rank=cycle_rank, genus=genus))
    isolated = []
    for i, profile in enumerate(profiles):
        check()
        if not profile['core_ports']:
            genus = 1 - profile['euler_characteristic']
            if genus < 0:
                raise ArithmeticError('a bordered bundle has negative handlebody genus')
            copies = profile['multiplicity']
            histogram[genus] += copies
            isolated.append(dict(base_profile=i, genus=genus, multiplicity=copies))
    euler = sum((1 - genus) * copies for genus, copies in histogram.items())
    expected = (summary['core_euler_characteristic'] +
                summary['bundle_euler_characteristic'] -
                summary['attachment_euler_characteristic'])
    if euler != expected:
        raise ArithmeticError('handlebody census violates source-cut Euler identity')
    return dict(histogram=[dict(genus=g, multiplicity=n) for g, n in sorted(histogram.items())],
                components=sum(histogram.values()), ball_components=histogram[0],
                all_balls=all(g == 0 for g in histogram), euler_characteristic=euler,
                joined_components=joined, isolated_bundles=isolated, attachments=edges), None


def normal_cut_handlebodies(triangulation, coordinates, *, max_cycles=None,
                           record_certificate=False, check=lambda: None):
    """Classify the whole supplied cut when the disk-gluing criterion succeeds.

    A COMPLETE result is an exact binary multiplicity census of handlebodies.
    An INCONCLUSIVE result is neither a knottedness nor a non-handlebody proof.
    Source validity is the established compact orientable one-torus contract.
    The six orbit discoveries share the cycle allowance; cancellation callbacks
    also cover the polynomial core and finite interface computations.
    """
    check()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    result = dict(status='INCONCLUSIVE', stats={},
                  trust='source cut handlebodies; no standalone knot verdict')
    parallelity = normal_cut_parallelity(triangulation, coordinates,
        max_cycles=max_cycles, record_certificate=record_certificate, check=check)
    result['stats']['parallelity'] = parallelity['stats']
    if parallelity['status'] != 'COMPLETE':
        result['reason'] = 'parallelity_budget_exhausted'
        return result
    if parallelity['geometry']['core']['handles3']:
        result['reason'] = 'core_has_three_handles'
        return result
    remaining = max_cycles
    if remaining is not None:
        remaining -= sum(s['orbit_cycles'] for s in parallelity['stats'].values())
    boundary = normal_parallelity_boundary_words(triangulation, coordinates,
        max_cycles=remaining, record_certificate=record_certificate, check=check)
    result['stats']['boundary'] = boundary['stats']
    if boundary['status'] != 'COMPLETE':
        result['reason'] = 'boundary_budget_exhausted'
        return result
    absorption = absorb_disk_bundles(parallelity['geometry'], parallelity['summary'],
                                     boundary['skeleton'], check=check)
    if absorption is None:
        result['reason'] = 'annular_core_attachment'
        return result
    augmented, absorption_proof, absorbed = absorption
    core = core_handlebody_certificate(augmented, check=check)
    result['stats']['core'] = core.get('stats', {})
    if core['status'] != 'COMPLETE':
        result['reason'] = core['reason']
        return result
    census, reason = _census(parallelity['geometry'], parallelity['summary'],
                            boundary['skeleton'], core['components'], check, absorbed)
    if census is None:
        result['reason'] = reason
        return result
    result.update(status='COMPLETE', census=census)
    if record_certificate:
        result['certificate'] = dict(schema='normal-cut-handlebodies-v1',
            parallelity=parallelity['certificate'], boundary=boundary['certificate'],
            core=core['certificate'], census=census)
        if absorbed:
            result['certificate'].update(schema='normal-cut-handlebodies-v2',
                                         absorption=absorption_proof)
    check()
    return result
