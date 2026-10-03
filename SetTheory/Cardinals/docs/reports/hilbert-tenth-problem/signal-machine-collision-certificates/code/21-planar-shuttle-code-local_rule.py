"""Independent radius-six cylinder evaluator, with no component traversal.

Input is a 169-bit window in row-major order, coordinates [-6,6]^2.
Patterns are independently encoded as strings here, not imported from the
component simulator. Each cylinder specifies all ones in an isolated shape
and all zeros in its radius-two halo. Only cylinders that can change the
central bit are compiled. The full shift has 2**169 possible input windows;
this finite Boolean expression represents the rule without enumerating them.
"""


def _points(text):
    return frozenset(tuple(map(int, pair.split(','))) for pair in text.split())


def _bit(x, y):
    if not -6 <= x <= 6 or not -6 <= y <= 6:
        raise ValueError("Cylinder exceeds the claimed radius")
    return 1 << ((y + 6) * 13 + x + 6)


def _compile(vertical_shift=0):
    recipes = (
        ("0,0 1,0", "1,0 2,0"),
        ("0,0 2,0", "-1,0 1,0"),
        ("0,0 1,0 3,0", "-1,0 1,0 4,1"),
        ("0,0 2,0 4,0", "0,1 3,1 4,1"),
    )
    births, removals = [], []
    for old_text, new_text in recipes:
        old, new = _points(old_text), _points(new_text)
        halo = {(x + dx, y + dy) for x, y in old
                for dx in range(-2, 3) for dy in range(-2, 3)}
        for target, sink in ((new - old, births), (old - new, removals)):
            for zx, zy in sorted(target):
                ones = sum(_bit(x - zx, y - zy - vertical_shift) for x, y in old)
                zeros = sum(_bit(x - zx, y - zy - vertical_shift)
                            for x, y in halo - old)
                sink.append((ones, zeros))
    return tuple(births), tuple(removals)


BIRTHS, REMOVALS = _compile()
DRIFT_BIRTHS, DRIFT_REMOVALS = _compile(vertical_shift=1)
CENTER = _bit(0, 0)
DRIFT_SOURCE = _bit(0, -1)
WINDOW_MASK = (1 << 169) - 1


def evaluate(mask):
    if type(mask) is not int or not 0 <= mask <= WINDOW_MASK:
        raise ValueError("Expected a nonnegative 169-bit integer")
    terms = REMOVALS if mask & CENTER else BIRTHS
    recognized = any(mask & ones == ones and mask & zeros == 0
                     for ones, zeros in terms)
    return int(not recognized) if mask & CENTER else int(recognized)


def drift_evaluate(mask):
    """F=upward-unit-shift composed with G, also of radius at most six."""
    if type(mask) is not int or not 0 <= mask <= WINDOW_MASK:
        raise ValueError("Expected a nonnegative 169-bit integer")
    terms = DRIFT_REMOVALS if mask & DRIFT_SOURCE else DRIFT_BIRTHS
    recognized = any(mask & ones == ones and mask & zeros == 0
                     for ones, zeros in terms)
    return int(not recognized) if mask & DRIFT_SOURCE else int(recognized)


def neighborhood(support, center):
    zx, zy = center
    return sum(_bit(x - zx, y - zy) for x, y in support
               if abs(x - zx) <= 6 and abs(y - zy) <= 6)


def step(support, search_radius=1):
    """Finite evaluation; radius 1 uses the proved displacement bound.

    Passing search_radius=6 independently searches every site that could
    possibly be nonzero for a general quiescent radius-six rule.
    """
    support = set(support)
    if type(search_radius) is not int or search_radius < 1:
        raise ValueError("search_radius must be a positive integer")
    candidates = {(x + dx, y + dy) for x, y in support
                  for dx in range(-search_radius, search_radius + 1)
                  for dy in range(-search_radius, search_radius + 1)}
    return {z for z in candidates if evaluate(neighborhood(support, z))}


def drift_step(support):
    support = set(support)
    candidates = {(x + dx, y + dy) for x, y in support
                  for dx in range(-2, 3) for dy in range(-2, 3)}
    return {z for z in candidates if drift_evaluate(neighborhood(support, z))}


def certificate():
    return {
        'alphabet': [0, 1], 'radius_upper_bound': 6,
        'window_bits': 169,
        'encoding': 'bit ((dy+6)*13+dx+6) for (dx,dy) in [-6,6]^2',
        'evaluation': ('If center=0, output=1 iff a birth cylinder matches; '
                       'if center=1, output=0 iff a removal cylinder matches.'),
        'cylinder_match': '(mask & ones)==ones and (mask & zeros)==0',
        'births': [{'ones': str(p), 'zeros': str(q)} for p, q in BIRTHS],
        'removals': [{'ones': str(p), 'zeros': str(q)} for p, q in REMOVALS],
        'recognition_rectangle': [-6, 6, -3, 2],
        'drifted_rule': {
            'radius_upper_bound': 6,
            'recognition_rectangle': [-6, 6, -4, 1],
            'baseline_source_bit': str(DRIFT_SOURCE),
            'evaluation': 'Same conditional expression, using baseline source bit.',
            'births': [{'ones': str(p), 'zeros': str(q)}
                       for p, q in DRIFT_BIRTHS],
            'removals': [{'ones': str(p), 'zeros': str(q)}
                         for p, q in DRIFT_REMOVALS],
        },
    }
