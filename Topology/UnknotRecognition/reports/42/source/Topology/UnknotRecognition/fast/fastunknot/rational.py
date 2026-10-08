"""Exact recognition for checked Montesinos presentations.

Input is the numerator closure of an integer tangle ``e`` followed by a
horizontal sum of finite rational tangles.  Each tangle is specified by an
ordinary continued fraction ``[a0, ..., ak] = a0 + 1/(a1 + ...)``.  Zero
intermediate denominators are interpreted projectively; a final infinite
tangle is outside this interface.  Coefficients must be literal integers.

The rational tangles are kept separate.  In particular, the determinant is
the UNREDUCED common-denominator numerator, not the numerator of the reduced
sum of their fractions.  Normalizing each tangle gives Seifert data
``(e; beta_i/alpha_i)`` with ``0 < beta_i < alpha_i``.  At most two exceptional
fibres gives a two-bridge link; for a knot its determinant is one exactly
when it is the unknot.  At least three exceptional fibres has nontrivial
orbifold fundamental-group quotient and cannot be the double cover of the
unknot.  The mathematical foundations are classical Montesinos/Seifert
theory; the accompanying article states the precise imported results.

``montesinos_certificate`` is arithmetic-only and handles binary coefficients
without expanding crossings.  ``montesinos_pd`` really builds the tangles,
their horizontal gluing, and the numerator closure; it does not infer a PD
from the final slope.  Diagram's checked constructor uses this function and
retains an immutable source record.  Arbitrary PDs carry no such promise.
"""
from __future__ import annotations


DEFAULT_MAX_CROSSINGS = 100_000


def canonical_source(e, tangles):
    """Validate and detach the source as ``(e, tuple(tuple(coeffs), ...))``."""
    from .diagram import DiagramError
    if type(e) is not int:
        raise DiagramError("the Montesinos integer tangle e must be an integer")
    if isinstance(tangles, (str, bytes, dict)):
        raise DiagramError("Montesinos tangles must be a list of continued fractions")
    try:
        entries = tuple(tangles)
        if any(isinstance(cf, (str, bytes, dict)) for cf in entries):
            raise TypeError("continued fractions must be integer sequences")
        values = tuple(tuple(coefficients) for coefficients in entries)
    except TypeError as exc:
        raise DiagramError("Montesinos tangles must be a list of continued fractions") from exc
    for coefficients in values:
        if not coefficients or any(type(a) is not int for a in coefficients):
            raise DiagramError("each continued fraction must contain one or more integers")
    return e, values


def _primitive(p, q):
    # A continued-fraction matrix is unimodular, so gcd(p,q)=1 already.
    return (-p, -q) if q < 0 or (q == 0 and p < 0) else (p, q)


def _evaluate_cf(coefficients, check=None):
    p, q = 1, 0
    max_bits = 1
    for a in reversed(coefficients):
        if check is not None:
            check()
        p, q = a * p + q, p
        max_bits = max(max_bits, abs(p).bit_length(), abs(q).bit_length())
    return (*_primitive(p, q), max_bits)


def continued_fraction(coefficients, *, check=None):
    """Return the primitive projective pair ``(p,q)`` of an ordinary CF."""
    _, (coefficients,) = canonical_source(0, [coefficients])
    p, q, _ = _evaluate_cf(coefficients, check)
    return p, q


def _data(e, tangles, *, check=None):
    from .diagram import DiagramError
    e, tangles = canonical_source(e, tangles)
    normalized_e = e
    slopes, exceptional = [], []
    max_bits = abs(e).bit_length()
    for coefficients in tangles:
        p, q, peak = _evaluate_cf(coefficients, check)
        if q == 0:
            raise DiagramError("a Montesinos summand must have finite final slope")
        a, beta = divmod(p, q)
        normalized_e += a
        slopes.append((p, q))
        if beta:
            exceptional.append((beta, q))
        max_bits = max(max_bits, peak, abs(p).bit_length(), q.bit_length(),
                       abs(normalized_e).bit_length())
    numerator, denominator = normalized_e, 1
    for beta, alpha in exceptional:
        if check is not None:
            check()
        numerator, denominator = numerator * alpha + beta * denominator, denominator * alpha
        max_bits = max(max_bits, abs(numerator).bit_length(), denominator.bit_length())
    return {
        "source": (e, tangles), "slopes": slopes, "normalized_e": normalized_e,
        "exceptional": exceptional, "signed_determinant": numerator,
        "denominator_product": denominator, "max_entry_bits": max_bits,
        "expanded_crossings": abs(e) + sum(abs(a) for cf in tangles for a in cf),
        "coefficient_count": 1 + sum(len(cf) for cf in tangles),
    }


def _encoded_integer(value):
    """Keep certificates JSON-safe beyond Python's decimal-digit ceiling."""
    return value if abs(value).bit_length() <= 1024 else {
        "hex": format(value, "x"), "bits": abs(value).bit_length()}


def _certificate(data):
    from .diagram import DiagramError
    determinant = abs(data["signed_determinant"])
    if determinant % 2 == 0:
        raise DiagramError("the Montesinos numerator closure is a link, not a knot")
    count = len(data["exceptional"])
    status = "UNKNOT" if count <= 2 and determinant == 1 else "KNOTTED"
    criterion = ("montesinos-orbifold-quotient" if count >= 3
                 else "montesinos-two-bridge-determinant")
    return {
        "version": 1, "status": status, "method": criterion,
        "input_scope": "numerator closure of an integer plus finite rational tangles",
        "normalized_e": _encoded_integer(data["normalized_e"]),
        "primitive_slopes": [[_encoded_integer(p), _encoded_integer(q)]
                             for p, q in data["slopes"]],
        "exceptional_fibres": [[_encoded_integer(beta), _encoded_integer(alpha)]
                               for beta, alpha in data["exceptional"]],
        "exceptional_count": count,
        "signed_determinant": _encoded_integer(data["signed_determinant"]),
        "determinant": _encoded_integer(determinant),
        "denominator_product": _encoded_integer(data["denominator_product"]),
        "expanded_crossings": _encoded_integer(data["expanded_crossings"]),
        "coefficient_count": data["coefficient_count"],
        "max_entry_bits": data["max_entry_bits"],
        "knot_component_test": "odd determinant",
    }


def montesinos_certificate(e, tangles, *, check=None):
    """Decide a supplied Montesinos knot without creating its crossing set.

    Invalid sources, infinite summands, and multi-component closures raise
    ``DiagramError``.  This is a complete test on its stated input class;
    it does not recognize whether an arbitrary PD is Montesinos.
    """
    return _certificate(_data(e, tangles, check=check))


def verify_montesinos_certificate(e, tangles, certificate):
    """Replay exact arithmetic using forward matrices and a product sum.

    This implementation does not reuse the production backwards-CF recurrence
    or its common-denominator accumulator.  It verifies the stated sufficient
    conditions, not the imported topological theorems.  No PD is authorized by
    this function alone; a Diagram source is separately checked by construction.
    """
    from .diagram import DiagramError
    if not isinstance(certificate, dict):
        return False
    try:
        e, tangles = canonical_source(e, tangles)
        slopes, exceptional, normalized_e = [], [], e
        # Reconstruct the same deterministic bit statistic from independently
        # evaluated slopes; it is not itself an input to the decision.
        max_bits = abs(e).bit_length()
        for cf in tangles:
            a, b, c, d = 1, 0, 0, 1
            for coefficient in cf:
                a, b, c, d = a * coefficient + b, a, c * coefficient + d, c
            p, q = _primitive(a, c)
            if q == 0:
                return False
            integer, beta = divmod(p, q)
            normalized_e += integer
            slopes.append((p, q))
            if beta:
                exceptional.append((beta, q))
            max_bits = max(max_bits, abs(p).bit_length(), q.bit_length(),
                           abs(normalized_e).bit_length())
            # Only the cost statistic uses the production evaluation order.
            # The slope and decision above use a separate forward matrix product.
            back_p, back_q = 1, 0
            max_bits = max(max_bits, 1)
            for coefficient in reversed(cf):
                back_p, back_q = coefficient * back_p + back_q, back_p
                max_bits = max(max_bits, abs(back_p).bit_length(), abs(back_q).bit_length())
        denominator = 1
        for _, alpha in exceptional:
            denominator *= alpha
        numerator = normalized_e * denominator
        for beta, alpha in exceptional:
            numerator += beta * (denominator // alpha)
        # Replay only the reported maximal intermediate bit size.  Correctness
        # above uses the independent full-product formula.
        partial_denominator = 1
        for index, (_, alpha) in enumerate(exceptional):
            partial_denominator *= alpha
            partial_numerator = normalized_e * partial_denominator
            for beta, divisor in exceptional[:index + 1]:
                partial_numerator += beta * (partial_denominator // divisor)
            max_bits = max(max_bits, abs(partial_numerator).bit_length(),
                           partial_denominator.bit_length())
        data = {
            "slopes": slopes, "normalized_e": normalized_e,
            "exceptional": exceptional, "signed_determinant": numerator,
            "denominator_product": denominator, "max_entry_bits": max_bits,
            "expanded_crossings": abs(e) + sum(abs(a) for cf in tangles for a in cf),
            "coefficient_count": 1 + sum(len(cf) for cf in tangles),
        }
        # Exact types reject booleans in integer fields as well as extra fields.
        def same(actual, expected):
            if type(actual) is not type(expected):
                return False
            if isinstance(expected, dict):
                return actual.keys() == expected.keys() and all(
                    same(actual[key], value) for key, value in expected.items())
            if isinstance(expected, list):
                return len(actual) == len(expected) and all(
                    same(left, right) for left, right in zip(actual, expected))
            return actual == expected
        return same(certificate, _certificate(data))
    except (DiagramError, TypeError, ValueError, ArithmeticError):
        return False


class _Builder:
    """Four-terminal tangle graph with an exact crossing-switch flag."""

    def __init__(self):
        self.rows = []
        self.parent = []

    def edge(self):
        result = len(self.parent)
        self.parent.append(result)
        return result

    def find(self, item):
        while self.parent[item] != item:
            self.parent[item] = self.parent[self.parent[item]]
            item = self.parent[item]
        return item

    def join(self, left, right):
        self.parent[self.find(left)] = self.find(right)

    def rational(self, coefficients):
        """Return terminals in NW,NE,SE,SW order, constructing actual twists."""
        upper, lower = self.edge(), self.edge()
        boundary = [upper, upper, lower, lower]
        switched = False
        # Each row stores a choice of which diagonal is under.  A global mirror
        # toggles that bit, avoiding quadratic repeated changes of old crossings.
        local_rows = []
        for index, coefficient in enumerate(reversed(coefficients)):
            if index:
                # A clockwise quarter turn sends F to -1/F; switching crossings
                # then negates it, producing the ordinary reciprocal 1/F.
                boundary = [boundary[3], boundary[0], boundary[1], boundary[2]]
                switched = not switched
            for _ in range(abs(coefficient)):
                out_lower, out_upper = self.edge(), self.edge()
                row = (boundary[1], boundary[2], out_lower, out_upper)
                local_rows.append((row, (coefficient < 0) ^ switched))
                boundary[1], boundary[2] = out_upper, out_lower
        for row, flip in local_rows:
            self.rows.append(row[1:] + row[:1] if flip ^ switched else row)
        return boundary

    def horizontal(self, left, right):
        self.join(left[1], right[0])
        self.join(left[2], right[3])
        return [left[0], right[1], right[2], left[3]]

    def numerator(self, boundary):
        self.join(boundary[0], boundary[1])
        self.join(boundary[3], boundary[2])
        pd = [tuple(self.find(label) for label in row) for row in self.rows]
        # Count components before discarding crossing-free wires.  PD validation
        # alone would not see an extra crossing-free component omitted from rows.
        strand_parent = list(range(len(self.parent)))

        def find(item):
            while strand_parent[item] != item:
                strand_parent[item] = strand_parent[strand_parent[item]]
                item = strand_parent[item]
            return item

        def join(left, right):
            strand_parent[find(left)] = find(right)

        for label in range(len(self.parent)):
            join(label, self.find(label))
        for row in self.rows:
            join(row[0], row[2])
            join(row[1], row[3])
        components = len({find(label) for label in range(len(self.parent))})
        return pd, components


def montesinos_pd(e, tangles, *, max_crossings=DEFAULT_MAX_CROSSINGS):
    """Build the actual closed PD and detached source, under an expansion cap.

    Use ``max_crossings=None`` to request an uncapped expansion.  The arithmetic
    API has no crossing expansion and is the appropriate path for huge binary
    coefficients.  The cap is checked before allocating any crossing objects.
    """
    from .diagram import DiagramError
    data = _data(e, tangles)
    _certificate(data)  # Reject links and unsupported infinite summands first.
    if max_crossings is not None and (type(max_crossings) is not int or max_crossings < 0):
        raise ValueError("max_crossings must be a nonnegative integer or None")
    if max_crossings is not None and data["expanded_crossings"] > max_crossings:
        raise DiagramError("Montesinos PD expansion exceeds max_crossings; "
                           "use the arithmetic montesinos_certificate API")
    e, tangles = data["source"]
    builder = _Builder()
    boundary = builder.rational((e,))
    for cf in tangles:
        boundary = builder.horizontal(boundary, builder.rational(cf))
    pd, components = builder.numerator(boundary)
    if components != 1:
        raise ArithmeticError("Montesinos arithmetic and constructed component count disagree")
    return pd, data["source"]


def build_montesinos_tangle(e, tangles, *, max_crossings=DEFAULT_MAX_CROSSINGS):
    """Return actual crossing rows and four boundary labels before closure.

    ``boundary`` is in NW, NE, SE, SW cyclic order.  Its labels, together with
    all ``pd`` occurrences, each occur exactly twice.  A crossing-free boundary
    arc therefore repeats one label in ``boundary``.  Source CFs have finite
    final slopes, but this routine does not require the numerator closure to
    be a knot.  A caller embedding a two-string tangle must additionally rule
    out closed components, since some sums can contain them.
    """
    from .diagram import DiagramError
    data = _data(e, tangles)
    if max_crossings is not None and (type(max_crossings) is not int or max_crossings < 0):
        raise ValueError("max_crossings must be a nonnegative integer or None")
    if max_crossings is not None and data["expanded_crossings"] > max_crossings:
        raise DiagramError("Montesinos tangle expansion exceeds max_crossings")
    e, tangles = data["source"]
    builder = _Builder()
    boundary = builder.rational((e,))
    for cf in tangles:
        boundary = builder.horizontal(boundary, builder.rational(cf))
    rows = [tuple(builder.find(label) for label in row) for row in builder.rows]
    boundary = tuple(builder.find(label) for label in boundary)
    labels = sorted({label for row in rows for label in row} | set(boundary))
    relabel = {label: index for index, label in enumerate(labels)}
    return {
        "pd": tuple(tuple(relabel[label] for label in row) for row in rows),
        "boundary": tuple(relabel[label] for label in boundary),
        "source": data["source"],
        "boundary_order": "NW,NE,SE,SW",
    }


def source_matches_pd(diagram, source):
    """Independently reconstruct a source before accepting serialized provenance."""
    from .diagram import Diagram, DiagramError
    try:
        e, tangles = source
        pd, normalized_source = montesinos_pd(e, tangles, max_crossings=diagram.crossings)
        rebuilt = Diagram.from_pd(pd)
    except (TypeError, ValueError, DiagramError):
        return None
    if len(rebuilt.pd) != len(diagram.pd) or any(
            a != b and a[2:] + a[:2] != b for a, b in zip(rebuilt.pd, diagram.pd)):
        return None
    return normalized_source
