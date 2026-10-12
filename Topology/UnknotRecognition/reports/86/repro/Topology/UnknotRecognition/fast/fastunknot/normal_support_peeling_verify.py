"""Independent sparse row replay for singleton-exposed normal matching rays.

The checker imports no propagation planner. It reconstructs source support,
then checks the triangular unit-pivot witness one original matching row at a
time. Unit pivots also certify that every coordinate is an integer multiple
of the seed, so the positive source seed equals its full coordinate gcd.
"""

from .integer_codec import encoded_integer
from .normal_surface_geometry import _prepare, _coordinates, NormalOrbitError


_FIELDS = {'schema', 'support', 'seed', 'steps', 'nullity'}
_BAD = object()


def _integer(value):
    try:
        return encoded_integer(value)
    except ValueError:
        return _BAD


def verify_support_ray(prepared, analysed, certificate, check=lambda: None):
    """Check a full ray rank witness in linear sparse-matrix work."""
    check()
    if (type(certificate) is not dict or set(certificate) != _FIELDS
            or certificate['schema'] != 'normal-support-ray-peeling-v1'
            or _integer(certificate['nullity']) != 1):
        return False
    source = [value for row in analysed['rows'] for value in row]
    support = [i for i, value in enumerate(source) if value > 0]
    raw = certificate['support']
    if type(raw) is not list or len(raw) != len(support):
        return False
    for claimed, expected in zip(raw, support):
        check()
        if _integer(claimed) != expected:
            return False
    if not support:
        return False
    present = set(support)
    seed = _integer(certificate['seed'])
    if seed is _BAD or seed not in present:
        return False
    steps = certificate['steps']
    if type(steps) is not list or len(steps) != len(support) - 1:
        return False
    equations = prepared['matching']
    # The positive nonzero source gives a lower bound of one for nullity.
    # These checks are independent of the producer's unknown-count arrays.
    for equation in equations:
        check()
        if sum(value * source[i] for i, value in equation.items() if i in present):
            return False
    known = {seed}
    for entry in steps:
        check()
        if type(entry) is not list or len(entry) != 2:
            return False
        row, pivot = (_integer(value) for value in entry)
        if (row is _BAD or pivot is _BAD or not 0 <= row < len(equations)
                or pivot not in present or pivot in known):
            return False
        missing = [i for i, value in equations[row].items()
                   if value and i in present and i not in known]
        if missing != [pivot] or abs(equations[row][pivot]) != 1:
            return False
        known.add(pivot)
    return known == present


def verify_normal_support_ray(triangulation, coordinates, certificate, *, check=lambda: None):
    """Rebuild finite geometry before independently checking a ray witness."""
    callback_error = [None]

    def checked():
        try:
            check()
        except BaseException as exc:
            callback_error[0] = exc
            raise

    checked()
    try:
        prepared = _prepare(triangulation, checked)
        analysed = _coordinates(prepared, coordinates, checked)
    except NormalOrbitError:
        if callback_error[0] is not None:
            raise
        return False
    return verify_support_ray(prepared, analysed, certificate, checked)
