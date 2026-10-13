"""Independent source and disk-gluing replay for normal-cut handlebody censuses."""

from collections import Counter

from .bundle_boundary_kernel_verify import replay_bundle_boundary_kernel
from .bundle_primitive_annuli_verify import replay_primitive_bundle_annuli
from .core_primitive_annuli_verify import replay_core_primitive_annuli
from .core_handlebody_verify import verify_core_handlebody_certificate
from .core_three_handle_reduction_verify import replay_core_three_handles
from .disk_bundle_absorption_verify import replay_disk_bundle_absorption
from .integer_codec import encoded_integer, certificate_equal
from .normal_cut_groups_verify import verify_normal_cut_group_handlebodies
from .normal_parallelity_verify import verify_normal_cut_parallelity
from .parallelity_boundary_words_verify import verify_parallelity_boundary_words
from .parallelity_boundary_moments_verify import verify_parallelity_moment_words


def _decode(value):
    if isinstance(value, dict):
        return {key: _decode(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_decode(item) for item in value]
    if isinstance(value, str) and value.lower().lstrip('+-').startswith('0x'):
        return encoded_integer(value)
    return value


def _recount(g, summary, skeleton, components, check, absorbed=frozenset(), primitive=None, core_annuli=None):
    primitive = {} if primitive is None else primitive
    core_annuli = {} if core_annuli is None else core_annuli
    core_deductions = Counter(core_annuli.values())
    profiles = summary['base_profiles']
    if any(p['boundary_components'] <= 0 for p in profiles):
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
    genus = {('core', c['id']): c['genus'] - core_deductions[c['id']] for c in components}
    genus.update({('base', i): 1 - p['euler_characteristic'] - primitive.get(i, 0)
                  for i, p in enumerate(profiles) if p['core_ports'] and i not in absorbed})
    neighbors = {node: [] for node in genus}
    edges = []
    for i, a in enumerate(skeleton['attachment_components']):
        check()
        ports = [abs(x) - 1 for x in a['word']]
        if a['kind'] == 'circle' and by_port[ports[0]] in absorbed:
            continue
        if a['kind'] != 'interval' and not (a['kind'] == 'circle' and (by_port[ports[0]] in primitive or i in core_annuli)):
            return None
        choices = {(by_port[p], core_port[p]) for p in ports}
        if len(choices) != 1:
            return None
        b, c = choices.pop()
        if i in core_annuli and core_annuli[i] != c:
            return None
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
    """Replay source and boundary proofs and the selected terminal independently.

    The operation cap includes powered Nielsen move records for signed-annulus
    packets (and Tietze pivots for Euler/group packets), in addition to orbit
    operation records. It does not count machine instructions.
    """
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be a nonnegative integer or None')
    fields = {'schema', 'parallelity', 'boundary', 'core', 'census'}
    if type(certificate) is not dict:
        return False
    version = certificate.get('schema')
    if version == 'normal-cut-euler-free-v1':
        return verify_normal_cut_group_handlebodies(triangulation, coordinates, certificate,
                                                    max_operations=max_operations, check=check)
    if version in ('normal-cut-handlebodies-v5', 'normal-cut-handlebodies-v6'):
        fields.remove('core')
        fields.add('kernel')
        if version == 'normal-cut-handlebodies-v6':
            fields.add('core_reduction')
    elif version in ('normal-cut-handlebodies-signed-annuli-v1',
                     'normal-cut-handlebodies-signed-annuli-v2'):
        fields.update(('absorption', 'signed_annuli'))
        if version == 'normal-cut-handlebodies-signed-annuli-v2':
            fields.add('core_reduction')
    elif version == 'normal-cut-handlebodies-v4':
        fields.update(('absorption', 'core_annuli'))
    elif version == 'normal-cut-handlebodies-v3':
        fields.update(('absorption', 'primitive_annuli'))
    elif version == 'normal-cut-handlebodies-v2':
        fields.add('absorption')
    elif version != 'normal-cut-handlebodies-v1':
        return False
    if set(certificate) != fields:
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
            boundary_names = (('census',) if b.get('schema') == 'native-moment-boundary-v2'
                              else ('vertex_partition', 'gap_cover'))
            for name in boundary_names:
                if b[name] is not None:
                    operations += len(b[name]['orbit_proof']['operations'])
            if version in ('normal-cut-handlebodies-signed-annuli-v1',
                           'normal-cut-handlebodies-signed-annuli-v2'):
                operations += sum(len(c['basis']['moves'])
                                  for c in certificate['signed_annuli']['components'])
        except (KeyError, TypeError):
            return False
        if operations > max_operations:
            return False
    if not verify_normal_cut_parallelity(triangulation, coordinates, p, check=check):
        return False
    boundary_verifier = (verify_parallelity_moment_words if b.get('schema') == 'native-moment-boundary-v2'
                         else verify_parallelity_boundary_words)
    if not boundary_verifier(triangulation, coordinates, b, check=check):
        return False
    # Large source integers may use the established exact hexadecimal codec.
    geometry, summary = _decode(p['geometry']), _decode(p['summary'])
    skeleton = _decode(b['skeleton'])
    if version in ('normal-cut-handlebodies-v6', 'normal-cut-handlebodies-signed-annuli-v2'):
        geometry = replay_core_three_handles(geometry, certificate['core_reduction'], check=check)
        if geometry is None:
            return False
    if version in ('normal-cut-handlebodies-v5', 'normal-cut-handlebodies-v6'):
        census = replay_bundle_boundary_kernel(geometry, summary, skeleton, certificate['kernel'], check=check)
        return census is not None and certificate_equal(certificate['census'], census)
    try:
        core_proof = _decode(certificate['core'])
    except ValueError:
        return False
    augmented, absorbed = geometry['core'], frozenset()
    primitive = {}
    if version == 'normal-cut-handlebodies-v3':
        primitive = replay_primitive_bundle_annuli(summary, skeleton,
                                                  certificate['primitive_annuli'], check=check)
        if primitive is None:
            return False
    deferred = primitive
    if version in ('normal-cut-handlebodies-v4', 'normal-cut-handlebodies-signed-annuli-v1',
                   'normal-cut-handlebodies-signed-annuli-v2'):
        deferred = {i for i, p in enumerate(summary['base_profiles'])
                    if (p['euler_characteristic'], p['boundary_components']) != (1, 1)}
    if version in ('normal-cut-handlebodies-v2', 'normal-cut-handlebodies-v3',
                   'normal-cut-handlebodies-v4', 'normal-cut-handlebodies-signed-annuli-v1',
                   'normal-cut-handlebodies-signed-annuli-v2'):
        replay = replay_disk_bundle_absorption(geometry, summary, skeleton,
                                               certificate['absorption'], primitive_bases=deferred, check=check)
        if replay is None:
            return False
        augmented, absorbed = replay
    if not verify_core_handlebody_certificate(augmented, core_proof, check=check):
        return False
    core_annuli = {}
    if version == 'normal-cut-handlebodies-v4':
        core_annuli = replay_core_primitive_annuli(geometry, summary, skeleton, augmented,
                            core_proof, certificate['core_annuli'], check=check)
        if core_annuli is None:
            return False
    elif version in ('normal-cut-handlebodies-signed-annuli-v1',
                     'normal-cut-handlebodies-signed-annuli-v2'):
        from .signed_annulus_basis_verify import replay_signed_annulus_basis
        try:
            signed_proof = _decode(certificate['signed_annuli'])
        except ValueError:
            return False
        core_annuli = replay_signed_annulus_basis(geometry, summary, skeleton, augmented,
                            core_proof, signed_proof, check=check)
        if core_annuli is None:
            return False
    expected = _recount(geometry, summary, skeleton, core_proof['components'], check, absorbed, primitive, core_annuli)
    check()
    return expected is not None and certificate_equal(certificate['census'], expected)
