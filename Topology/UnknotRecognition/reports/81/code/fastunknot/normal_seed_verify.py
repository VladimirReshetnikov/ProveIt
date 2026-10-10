"""Check source-bound disc, annulus-cap or planar-cap proofs without seed discovery."""
from .diagram import Diagram, DiagramError
from .diagram_exterior_verify import verify_diagram_exterior
from .normal_disk_kernel import verify_normal_disk_count_certificate
from .integer_codec import certificate_equal, encoded_integer


def verify_normal_seed_certificate(diagram, certificate, *, check=lambda: None):
    check()
    if type(certificate) is dict and certificate.get('schema') == 'diagram-shelling-witness-v1':
        from .normal_shelling_verify import verify_shelling_certificate
        return verify_shelling_certificate(diagram, certificate, check=check)
    if type(certificate) is dict and certificate.get('schema') == 'diagram-cocycle-planar-v1':
        from .normal_planar_verify import inspect_planar_certificate
        return inspect_planar_certificate(diagram, certificate, check=check) is not None
    if type(certificate) is dict and certificate.get('schema') == 'diagram-cocycle-annulus-v1':
        from .normal_annulus_verify import inspect_annulus_certificate
        return inspect_annulus_certificate(diagram, certificate, check=check) is not None
    if type(certificate) is dict and certificate.get('schema') == 'diagram-cocycle-disc-v1':
        from .normal_cocycle_verify import inspect_cocycle_certificate
        summary = inspect_cocycle_certificate(diagram, certificate, check=check)
        return summary is not None and summary['compressing_discs'] == 1
    if (type(certificate) is not dict
            or set(certificate) != {'schema', 'input_pd', 'triangulation', 'coordinates', 'disc_certificate'}
            or certificate['schema'] != 'diagram-normal-disc-v1'):
        return False
    try:
        source = Diagram.from_pd(diagram.pd)
    except (DiagramError, AttributeError, TypeError):
        return False
    if not certificate_equal(certificate['input_pd'], [list(row) for row in source.pd]):
        return False
    raw, vector, proof = (certificate[key] for key in ('triangulation', 'coordinates', 'disc_certificate'))
    if (not verify_diagram_exterior(source, raw, check=check)
            or not verify_normal_disk_count_certificate(raw, vector, proof, check=check)):
        return False
    # A valid zero-count certificate is not an unknot certificate.
    try:
        count = encoded_integer(proof['compressing_disk_components'])
    except (ValueError, KeyError, TypeError):
        return False
    check()
    return count > 0
