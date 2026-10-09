"""Bind a supplied-vector ray-block disc certificate to a classical diagram.

The canonical Weeks exterior and its independent local-coordinate checker
are inherited from the maintained recognizer. A zero count is inconclusive:
this module does not search the normal solution space for another surface.
"""

from .diagram import Diagram, DiagramError
from .diagram_exterior import diagram_exterior
from .diagram_exterior_verify import verify_diagram_exterior
from .integer_codec import certificate_equal, encoded_integer
from .normal_ray_blocks import normal_ray_block_disk_count
from .normal_ray_blocks_verify import verify_normal_ray_block_disk_certificate


def certify_diagram_ray_disks(diagram, coordinates, *, subdivision='pulling',
                              max_cycles=None, periodic_rule='fine_wilf',
                              check=lambda: None):
    """Return a checked UNKNOT certificate or INCONCLUSIVE for supplied data.

    Coordinates must describe a surface in ``diagram_exterior(diagram)`` with
    the requested subdivision. Construction, count and source replay are all
    included. Invalid vectors raise a geometry error; they are not negatives.
    """
    check()
    source = Diagram.from_pd(diagram.pd)
    raw = diagram_exterior(source, subdivision=subdivision, check=check)
    answer = normal_ray_block_disk_count(raw, coordinates, max_cycles=max_cycles,
        periodic_rule=periodic_rule, check=check, record_certificate=True)
    if answer['status'] != 'COMPLETE':
        return dict(status='INCONCLUSIVE', reason=answer['reason'], stats=answer['stats'])
    if not answer['contains_compressing_disk']:
        return dict(status='INCONCLUSIVE',
            reason='the supplied normal vector contains no essential disc',
            stats=answer['stats'])
    proof = dict(schema='diagram-ray-disks-v1', input_pd=[list(row) for row in source.pd],
        triangulation=raw, coordinates=coordinates, disc_certificate=answer['certificate'])
    if not verify_diagram_ray_disk_certificate(source, proof, check=check):
        raise ArithmeticError('source-bound ray-disc certificate failed replay')
    check()
    return dict(status='UNKNOT', method='source-bound-ray-disc', certificate=proof,
                compressing_disk_components=answer['compressing_disk_components'],
                stats=answer['stats'])


def verify_diagram_ray_disk_certificate(diagram, certificate, *, check=lambda: None):
    """Verify source correspondence and positive disc evidence without search."""
    callback_error = [None]

    def checked():
        try:
            check()
        except BaseException as exc:
            callback_error[0] = exc
            raise

    checked()
    fields = {'schema', 'input_pd', 'triangulation', 'coordinates', 'disc_certificate'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != 'diagram-ray-disks-v1'):
        return False
    try:
        source = Diagram.from_pd(diagram.pd)
    except (DiagramError, AttributeError, TypeError):
        return False
    if not certificate_equal(certificate['input_pd'], [list(row) for row in source.pd]):
        return False
    raw, coordinates, disc = (certificate[key] for key in
                             ('triangulation', 'coordinates', 'disc_certificate'))
    if not verify_diagram_exterior(source, raw, check=checked):
        return False
    if not verify_normal_ray_block_disk_certificate(raw, coordinates, disc, check=checked):
        if callback_error[0] is not None:
            raise callback_error[0]
        return False
    # The strict disc checker has already validated the count's syntax.
    return encoded_integer(disc['compressing_disk_components']) > 0
