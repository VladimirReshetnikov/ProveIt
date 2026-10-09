"""Linear singleton propagation certifying a one-dimensional matching support.

A single positive seed and rows with one as-yet unknown coordinate having
unit coefficient determine every supported coordinate as an integer multiple
of the seed. No coordinate values are propagated: the validated source gives
existence, while the ordered transcript certifies uniqueness and primitivity
after division by the seed. In particular, the coordinate gcd is the seed.
"""

from collections import deque

from .normal_surface_geometry import _prepare, _coordinates


def peel_support_ray(prepared, analysed, check=lambda: None):
    """Return a ray certificate, or None if one minimum-bit seed does not close.

    Each supported column is processed once and each matrix incidence once.
    Failure is only failure of this sufficient row-exposure criterion. Empty
    support returns None because its matching space has dimension zero.
    """
    check()
    source = [value for row in analysed['rows'] for value in row]
    if any(type(value) is not int or value < 0 for value in source):
        raise ValueError('analysed coordinates must be nonnegative integers')
    support = [i for i, value in enumerate(source) if value]
    if not support:
        return None
    seed = min(support, key=lambda i: (source[i].bit_length(), i))
    present = set(support)
    incident = {i: [] for i in support}
    remaining, only = [], []
    for index, equation in enumerate(prepared['matching']):
        check()
        if any(type(i) is not int or not 0 <= i < len(source)
               or type(value) is not int for i, value in equation.items()):
            raise ValueError('matching row violates the finite normal-row contract')
        columns = [i for i, value in equation.items() if value and i in present]
        if sum(equation[i] * source[i] for i in columns):
            raise ValueError('analysed source fails the matching equations')
        remaining.append(len(columns))
        xor = 0
        for i in columns:
            incident[i].append(index)
            xor ^= i
        only.append(xor)
    queue, known, steps = deque([seed]), {seed}, []
    while queue:
        check()
        current = queue.popleft()
        for index in incident[current]:
            check()
            remaining[index] -= 1
            only[index] ^= current
            if remaining[index] == 1:
                target = only[index]
                if target not in known and abs(prepared['matching'][index][target]) == 1:
                    known.add(target)
                    queue.append(target)
                    steps.append([index, target])
    if len(known) != len(support):
        return None
    return dict(schema='normal-support-ray-peeling-v1', support=support,
                seed=seed, steps=steps, nullity=1)


def peel_normal_support_ray(triangulation, coordinates, *, check=lambda: None):
    """Validate a finite supplied normal surface and try the linear rank gate."""
    prepared = _prepare(triangulation, check)
    analysed = _coordinates(prepared, coordinates, check)
    return peel_support_ray(prepared, analysed, check)
