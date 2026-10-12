"""Independent source and disk-gluing replay for normal-cut handlebody censuses."""

from collections import Counter

from .core_handlebody_verify import verify_core_handlebody_certificate
from .integer_codec import encoded_integer, certificate_equal
from .normal_parallelity_verify import verify_normal_cut_parallelity
from .parallelity_boundary_words_verify import verify_parallelity_boundary_words


def _decode(value):
    if isinstance(value, dict):
        return {key: _decode(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_decode(item) for item in value]
    if isinstance(value, str) and value.startswith(('0x', '-0x')):
        return encoded_integer(value)
    return value


def _recount(g, summary, skeleton, components, check):
    profiles = summary['base_profiles']
    if any(p['boundary_components'] <= 0 for p in profiles):
        return None
    if any(a['kind'] != 'interval' for a in skeleton['attachment_components']):
        return None
    vertex_component = {}
    for c in components:
        for v in c['zero_handles']:
            vertex_component[v] = c['id']
    by_port = {}
    for i, p in enumerate(profiles):
        for port in p['core_ports']:
            by_port[port] = i
    core_port = {}
    for port in g['ports']:
        if port['core_dimension'] == 0:
            v = port['core_handle']
        elif port['core_dimension'] == 1:
            v = g['core']['handles1'][port['core_handle']]['ends'][0]
        else:
            return None
        core_port[port['id']] = vertex_component[v]
    genus = {('core', c['id']): c['genus'] for c in components}
    genus.update({('base', i): 1 - p['euler_characteristic']
                  for i, p in enumerate(profiles) if p['core_ports']})
    neighbors = {node: [] for node in genus}
    edges = []
    for i, a in enumerate(skeleton['attachment_components']):
        check()
        ports = [abs(x) - 1 for x in a['word']]
        choices = {(by_port[p], core_port[p]) for p in ports}
        if len(choices) != 1:
            return None
        b, c = choices.pop()
        edges.append(dict(attachment=i, base_profile=b, core_component=c))
        neighbors['base', b].append(('core', c))
        neighbors['core', c].append(('base', b))
    unseen = set(neighbors)
    joined, histogram = [], Counter()
    while unseen:
        check()
        start = min(unseen)
        todo, visited = [start], set()
        while todo:
            node = todo.pop()
            if node in visited:
                continue
            visited.add(node)
            todo.extend(neighbors[node])
        unseen.difference_update(visited)
        attached = [i for i, e in enumerate(edges) if ('base', e['base_profile']) in visited]
        beta = len(attached) - len(visited) + 1
        value = sum(genus[v] for v in visited) + beta
        if beta < 0 or value < 0:
            return None
        histogram[value] += 1
        joined.append(dict(core_components=sorted(v[1] for v in visited if v[0] == 'core'),
                           base_profiles=sorted(v[1] for v in visited if v[0] == 'base'),
                           attachments=attached, cycle_rank=beta, genus=value))
    isolated = []
    for i, p in enumerate(profiles):
        if not p['core_ports']:
            value = 1 - p['euler_characteristic']
            if value < 0:
                return None
            histogram[value] += p['multiplicity']
            isolated.append(dict(base_profile=i, genus=value, multiplicity=p['multiplicity']))
    euler = sum(n * (1 - g) for g, n in histogram.items())
    source = summary['core_euler_characteristic'] + summary['bundle_euler_characteristic']
    if euler != source - summary['attachment_euler_characteristic']:
        return None
    return dict(histogram=[dict(genus=g, multiplicity=n) for g, n in sorted(histogram.items())],
                components=sum(histogram.values()), ball_components=histogram[0],
                all_balls=all(g == 0 for g in histogram), euler_characteristic=euler,
                joined_components=joined, isolated_bundles=isolated, attachments=edges)


def verify_normal_cut_handlebodies(triangulation, coordinates, certificate, *,
                                  max_operations=None, check=lambda: None):
    """Replay all six orbit proofs and the independent finite geometric checks."""
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be a nonnegative integer or None')
    fields = {'schema', 'parallelity', 'boundary', 'core', 'census'}
    if type(certificate) is not dict or set(certificate) != fields:
        return False
    if certificate['schema'] != 'normal-cut-handlebodies-v1':
        return False
    p, b = certificate['parallelity'], certificate['boundary']
    if type(p) is not dict or type(b) is not dict:
        return False
    if max_operations is not None:
        try:
            operations = 0
            for name in ('vertex_selector', 'boundary_selector', 'polygon_weights', 'fibre_cover'):
                proof = p[name]
                if name.endswith('selector'):
                    proof = proof['weighted_certificate']
                operations += len(proof['orbit_proof']['operations'])
            for name in ('vertex_partition', 'gap_cover'):
                if b[name] is not None:
                    operations += len(b[name]['orbit_proof']['operations'])
        except (KeyError, TypeError):
            return False
        if operations > max_operations:
            return False
    if not verify_normal_cut_parallelity(triangulation, coordinates, p, check=check):
        return False
    if not verify_parallelity_boundary_words(triangulation, coordinates, b, check=check):
        return False
    # Large source integers may use the established exact hexadecimal codec.
    geometry, summary = _decode(p['geometry']), _decode(p['summary'])
    skeleton = _decode(b['skeleton'])
    if not verify_core_handlebody_certificate(geometry['core'], certificate['core'], check=check):
        return False
    expected = _recount(geometry, summary, skeleton, certificate['core']['components'], check)
    check()
    return expected is not None and certificate_equal(certificate['census'], expected)
