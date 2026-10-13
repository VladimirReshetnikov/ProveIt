"""Independent source, presentation, Tietze, and Euler replay for group terminals."""

from collections import Counter

from .free_group_elimination_verify import replay_free_group
from .integer_codec import certificate_equal, encoded_integer
from .normal_parallelity_verify import verify_normal_cut_parallelity
from .parallelity_boundary_moments_verify import verify_parallelity_moment_words
from .parallelity_boundary_words_verify import verify_parallelity_boundary_words
from .source_cut_group_verify import verify_disk_cut_presentation


def _decoded(value):
    if isinstance(value, list):
        return [_decoded(item) for item in value]
    if isinstance(value, dict):
        return {key: _decoded(item) for key, item in value.items()}
    if isinstance(value, str) and value.lower().lstrip('+-').startswith('0x'):
        return encoded_integer(value)
    return value


def verify_normal_cut_group_handlebodies(triangulation, coordinates, certificate, *,
                                         max_operations=None, check=lambda: None):
    """Replay all source traces and finite certificates without invoking search.

    max_operations bounds the aggregate number of recorded orbit operations
    and Tietze pivots; it is not a machine-instruction counter.  Cooperative
    callback exceptions and invalid-source exceptions propagate.
    """
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be a nonnegative integer or None')
    fields = {'schema', 'parallelity', 'boundary', 'presentation', 'groups', 'census'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != 'normal-cut-euler-free-v1'):
        return False
    p, b = certificate['parallelity'], certificate['boundary']
    if type(p) is not dict or type(b) is not dict or type(certificate['groups']) is not list:
        return False
    if max_operations is not None:
        try:
            operations = 0
            for name in ('vertex_selector', 'boundary_selector', 'polygon_weights', 'fibre_cover'):
                proof = p[name]['weighted_certificate'] if name.endswith('selector') else p[name]
                operations += len(proof['orbit_proof']['operations'])
            names = (('census',) if b.get('schema') == 'native-moment-boundary-v2'
                     else ('vertex_partition', 'gap_cover'))
            for name in names:
                if b[name] is not None:
                    operations += len(b[name]['orbit_proof']['operations'])
            operations += sum(len(g['proof']['moves']) for g in certificate['groups'])
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
    try:
        geometry, summary = _decoded(p['geometry']), _decoded(p['summary'])
        skeleton, presentation = _decoded(b['skeleton']), _decoded(certificate['presentation'])
        groups = _decoded(certificate['groups'])
    except (ValueError, TypeError):
        return False
    if not verify_disk_cut_presentation(geometry, summary, skeleton, presentation, check=check):
        return False
    parts = presentation['components']
    if len(groups) != len(parts):
        return False
    histogram, joined, rank_sum, trivial_sum = Counter(), [], 0, 0
    for component, group in zip(parts, groups):
        check()
        if (type(group) is not dict or set(group) != {'component', 'proof'}
                or type(group['component']) is not int or group['component'] != component['id']):
            return False
        replay = replay_free_group(component['generators'], component['relators'],
                                    group['proof'], check=check)
        if replay is None:
            return False
        rank = replay['free_rank']
        rank_sum += rank
        trivial_sum += replay['trivial_relators']
        histogram[rank] += 1
        joined.append(dict(id=component['id'], core_components=component['core_components'],
                           interval_bases=component['interval_bases'],
                           annular_bases=component['annular_bases'], genus=rank))
    isolated = presentation['isolated_ball_count']
    histogram[0] += isolated
    count = len(parts) + isolated
    source_euler = (summary['core_euler_characteristic'] + summary['bundle_euler_characteristic']
                    - summary['attachment_euler_characteristic'])
    if count - rank_sum != source_euler:
        return False
    if trivial_sum != len(geometry['core']['handles3']):
        return False
    expected = dict(histogram=[dict(genus=g, multiplicity=n) for g, n in sorted(histogram.items()) if n],
                    components=count, ball_components=histogram[0],
                    all_balls=all(g == 0 for g, n in histogram.items() if n),
                    euler_characteristic=source_euler, free_rank_sum=rank_sum,
                    joined_components=joined, isolated_ball_count=isolated)
    return certificate_equal(certificate['census'], expected)
