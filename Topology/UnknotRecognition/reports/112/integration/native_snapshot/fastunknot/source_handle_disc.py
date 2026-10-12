"""Bind a geometric cancellation/cocore certificate to a canonical knot exterior."""
from .diagram import Diagram, DiagramError
from .diagram_exterior_verify import verify_diagram_exterior
from .integer_codec import certificate_equal
from .source_handle_reduction_verify import verify_source_handle_reduction


def verify_handle_disc_certificate(diagram, certificate, *, check=lambda:None):
    check()
    if type(certificate)is not dict or set(certificate)!={'schema','input_pd','triangulation','handle_certificate'} or certificate['schema']!='diagram-handle-disc-v1':return False
    try:source=Diagram.from_pd(diagram.pd)
    except (DiagramError,AttributeError,TypeError):return False
    if not certificate_equal(certificate['input_pd'],[list(row)for row in source.pd]):return False
    raw=certificate['triangulation'];proof=certificate['handle_certificate']
    if not verify_diagram_exterior(source,raw,check=check):return False
    if not verify_source_handle_reduction(raw,proof,check=check):return False
    # An authenticated partial reduction without a cocore witness is no verdict.
    check();return proof['compressing_disc']is not None
