"""Source-authenticated replay of the dual-reduced boundary-kernel census."""

from .bundle_boundary_kernel_verify import replay_bundle_boundary_kernel
from .integer_codec import certificate_equal
from .normal_cut_handlebodies_verify import _decode
from .normal_parallelity_verify import verify_normal_cut_parallelity
from .parallelity_boundary_words_verify import verify_parallelity_boundary_words
from .source_core_dual_verify import replay_source_core_dual


def verify_normal_cut_dual(triangulation, coordinates, certificate, *,
                           max_operations=None, check=lambda: None):
    """Check source packets, dual forest, geometric kernel, and exact census."""
    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('max_operations must be a nonnegative integer or None')
    expected = {'schema', 'parallelity', 'boundary', 'dual', 'kernel', 'census'}
    if (type(certificate) is not dict or set(certificate) != expected or
            certificate['schema'] != 'normal-cut-handlebodies-v6'):
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
    try:
        geometry, summary, skeleton = _decode(p['geometry']), _decode(p['summary']), _decode(b['skeleton'])
        dual_proof = _decode(certificate['dual'])
    except ValueError:
        return False
    reduced = replay_source_core_dual(geometry, dual_proof, check=check)
    if reduced is None:
        return False
    census = replay_bundle_boundary_kernel(reduced, summary, skeleton,
                                           certificate['kernel'], check=check)
    check()
    return census is not None and certificate_equal(certificate['census'], census)
