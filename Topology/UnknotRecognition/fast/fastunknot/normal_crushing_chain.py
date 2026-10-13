"""Source-authenticated shrinking chains for classical knot exteriors.

Each positive primitive normal extreme ray is connected. In a classical knot
exterior it is a sphere or disc. Jaco--Rubinstein crushing, as specialized by
Burton--Ozlen, leaves the same exterior as the torus-boundary component, or
its absence certifies the unknot. This module imports no discovery backend
for verification, and a partial REDUCED chain is not a recognition verdict.
"""
from .diagram import Diagram, DiagramError
from .diagram_exterior_verify import verify_diagram_exterior
from .boundary_shellings_verify import verify_boundary_shellings
from .integer_codec import certificate_equal
from .normal_crushing_verify import verify_normal_crushing
from .boundary_unlayer_verify import verify_boundary_unlayering
from .normal_pachner32_verify import verify_normal_pachner32


class _CallbackRaised(BaseException):
    def __init__(self, error):
        self.error = error
        self.traceback = error.__traceback__


def _safe_call(function, check, *args, **kwargs):
    def guarded():
        try:
            check()
        except BaseException as error:
            raise _CallbackRaised(error) from None
    try:
        return function(*args, check=guarded, **kwargs)
    except _CallbackRaised as interruption:
        raise interruption.error.with_traceback(interruption.traceback) from None


def verify_crushing_chain(diagram, certificate, *, check=lambda: None):
    """Verify the original diagram, optional shellings, and every shrinking step.

    Version 1 accepts normal crushes only. Version 2 additionally accepts
    independently checked inverse boundary layers, which preserve the compact
    manifold and always have a nonempty, strictly smaller successor.
    Version 3 also accepts source-bound relative-boundary Pachner 3-2 moves.

    A true UNKNOT certificate proves triviality. A true REDUCED certificate
    authenticates only the supplied smaller exterior. It must not be consumed
    as either an unknot or a knottedness verdict. Malformed packets return False;
    caller exceptions, including malformed-input exception classes, propagate.
    """
    return _safe_call(_verify_crushing_chain, check, diagram, certificate)


def _verify_crushing_chain(diagram, certificate, *, check):
    check()
    try:
        source = Diagram.from_pd(diagram.pd)
        fields = {'schema', 'input_pd', 'source_triangulation', 'shelling',
                  'steps', 'status', 'triangulation'}
        if (type(certificate) is not dict or set(certificate) != fields or
                certificate['schema'] not in ('diagram-crushing-v1', 'diagram-crushing-v2',
                                              'diagram-crushing-v3') or
                certificate['status'] not in ('REDUCED', 'UNKNOT') or
                type(certificate['steps']) is not list or
                not certificate_equal(certificate['input_pd'], [list(r) for r in source.pd])):
            return False
        current = certificate['source_triangulation']
        if not verify_diagram_exterior(source, current, check=check):
            return False
        shelling = certificate['shelling']
        if shelling is not None:
            if (type(shelling) is not dict or set(shelling) != {'triangulation','moves'} or
                    not verify_boundary_shellings(current, shelling['triangulation'],
                                                  shelling['moves'], check=check)):
                return False
            current = shelling['triangulation']
        if len(certificate['steps']) > len(current['tetrahedra']):
            return False
        for step in certificate['steps']:
            check()
            if current is None or type(step) is not dict:
                return False
            operation = step.get('schema')
            if operation == 'normal-boundary-unlayer-v1':
                if certificate['schema'] == 'diagram-crushing-v1':
                    return False
                verifier = verify_boundary_unlayering
            elif operation == 'normal-pachner-32-v1':
                if certificate['schema'] != 'diagram-crushing-v3':
                    return False
                verifier = verify_normal_pachner32
            else:
                verifier = verify_normal_crushing
            if not verifier(current, step, check=check):
                return False
            successor = step['successor']
            if successor is not None and len(successor['tetrahedra']) >= len(current['tetrahedra']):
                return False
            current = successor
        expected_status = 'UNKNOT' if current is None else 'REDUCED'
        check()
        return certificate['status'] == expected_status and certificate_equal(
            certificate['triangulation'], current)
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError, DiagramError):
        return False


def make_crushing_chain(diagram, coordinates_sequence, *, shelling=None, check=lambda: None):
    """Build a chain from supplied rays, independently replaying every quotient.

    No ray search or completeness assertion is implicit in this constructor.
    Each coordinate array is relative to the preceding selected successor.
    Optional shelling is exactly {'triangulation': ..., 'moves': ...}.
    """
    return _safe_call(_make_crushing_chain, check, diagram, coordinates_sequence, shelling=shelling)


def _make_crushing_chain(diagram, coordinates_sequence, *, shelling, check):
    # Constructors are deliberately absent from the verifier's import graph.
    from .diagram_exterior import diagram_exterior
    from .normal_crushing import crush_normal_ray
    source = Diagram.from_pd(diagram.pd)
    initial = diagram_exterior(source, check=check)
    current = initial
    if shelling is not None:
        if (type(shelling) is not dict or set(shelling) != {'triangulation','moves'} or
                not verify_boundary_shellings(initial, shelling['triangulation'],
                                              shelling['moves'], check=check)):
            raise ValueError('invalid source boundary-shelling certificate')
        current = shelling['triangulation']
    steps = []
    for coordinates in coordinates_sequence:
        check()
        if current is None:
            raise ValueError('crushing chain continues after terminal quotient')
        result = crush_normal_ray(current, coordinates, check=check)
        packet = result['certificate']
        if not verify_normal_crushing(current, packet, check=check):
            raise ArithmeticError('independent crushing replay failed')
        steps.append(packet)
        current = packet['successor']
    certificate = dict(schema='diagram-crushing-v1', input_pd=[list(r) for r in source.pd],
        source_triangulation=initial, shelling=shelling, steps=steps,
        status='UNKNOT' if current is None else 'REDUCED', triangulation=current)
    if not verify_crushing_chain(source, certificate, check=check):
        raise ArithmeticError('independent source-bound crushing chain replay failed')
    return certificate
