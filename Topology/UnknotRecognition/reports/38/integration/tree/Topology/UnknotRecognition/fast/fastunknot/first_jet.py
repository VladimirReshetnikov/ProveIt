"""Read-only first-jet queries before cobordism-valued cancellation.

For a whole component on one nonempty matching, let A be its scalar
differential and B the sum of its singleton-dot coefficient matrices.
The two binary ranks compute

    t = N - 2 rank(A),       kappa = N - rank([[A, 0], [B, A]]).

These are invariant under scalar-unit cancellation.  A knot completion has
total characteristic-two Khovanov rank kappa times the completed matching's
rank.  Moreover kappa == 1 implies rank equality for *every* classical link
completion, by primitive-interval rigidity.  kappa == 0 means the original
relative component is contractible.  No nontriviality claim for arbitrary
link completions is made when kappa >= 2.

The caller must supply a genuine chain complex and relative summand.  The
optional audit checks only A squared and AB + BA, not the full polynomial
differential or geometric provenance.  Mixed matching components are declined.
Local budget exhaustion changes nothing and may be followed by ordinary
cancellation; the caller's global deadline has priority.
"""
from collections import defaultdict


class FirstJetBudget(Exception):
    """Optional read-only observation exhausted its local work allowance."""


class _Work:
    def __init__(self, scan, limit, check):
        if limit is not None and (type(limit) is not int or limit < 0):
            raise ValueError("first-jet max_work must be a nonnegative integer or None")
        self.scan_check = getattr(scan, '_check', lambda: None)
        self.check = check
        self.limit, self.used = limit, 0

    def __call__(self, amount=1):
        # A global ScanLimit must not be converted into optional exhaustion.
        self.scan_check()
        if self.check is not None:
            self.check()
        if self.limit is not None and self.used + amount > self.limit:
            raise FirstJetBudget("first-jet observation allowance exhausted")
        self.used += amount


def _rank(columns, work):
    pivots = {}
    for column in columns:
        work()
        while column:
            work(max(1, (column.bit_length() + 63) // 64))
            lead = column.bit_length() - 1
            old = pivots.get(lead)
            if old is None:
                pivots[lead] = column
                break
            column ^= old
    return len(pivots)


def _linear_parity(value, work):
    """Select monomials of degree exactly one, never all monomial parity."""
    result = 0
    position = 1
    length = value.bit_length()
    # In packed polynomial storage the singleton monomial positions are
    # 1, 2, 4, ... .  Reading just these avoids enumerating a dense tail of
    # irrelevant higher-degree monomials.
    while position < length:
        work(max(1, (length - position + 63) // 64))
        result ^= (value >> position) & 1
        position <<= 1
    return result


def _apply(columns, vector, work):
    value = 0
    while vector:
        work()
        low = vector & -vector
        value ^= columns[low.bit_length() - 1]
        vector ^= low
    return value


def first_jet_profile(scan, group, *, max_work=1_000_000, check=None,
                      audit=False):
    """Return a first-jet certificate for a whole one-matching component.

    This query never changes scan.  Scalar units are accepted.  Return None
    for mixed matchings or an empty geometric matching.  Invalid vertices,
    external differential attachments, degree errors and out-of-domain
    coefficients raise ValueError.  FirstJetBudget is an inconclusive local
    limit, whereas the scan's own global exception propagates unchanged.

    ``kind`` is ``contractible``, ``matching-rank``, or ``knot-multiplier``.
    Only the first kind is an open homotopy-zero certificate.  The second
    preserves total rank under all nonempty classical link completions.
    For the last, the multiplier is certified only after checking that the
    actual matching completion is a knot.  The result is not itself a knot
    verdict, and stores no replacement differential or erased grading.

    Work units charge input traversal, polynomial terms, and binary work in
    64-bit chunks.  They are an operation allowance, not a wall-clock or
    byte-memory bound.  ``audit=True`` checks the two first-jet identities;
    it must not be mistaken for a full d-squared or provenance certificate.
    """
    work = _Work(scan, max_work, check)
    work()
    group = tuple(group)
    members = set(group)
    if not group or len(group) != len(members):
        raise ValueError("invalid first-jet block vertices")
    for vertex in group:
        work()
        if (type(vertex) is not int or not 0 <= vertex < len(scan.mid)
                or scan.mid[vertex] is None):
            raise ValueError("invalid live first-jet block vertex")
        for other in scan.out[vertex]:
            work()
            if other not in members:
                raise ValueError("first-jet block has external differential attachments")
        for other in scan.inc[vertex]:
            work()
            if other not in members:
                raise ValueError("first-jet block has external differential attachments")
    matching = scan.mid[group[0]]
    if any(scan.mid[vertex] != matching for vertex in group):
        return None
    variables = len(scan.algebra.pairs[matching])
    if not variables:
        return None

    layers = defaultdict(list)
    for vertex in group:
        work()
        if type(scan.deg[vertex]) is not int:
            raise ValueError("first-jet differential has a noninteger degree")
        layers[scan.deg[vertex]].append(vertex)
    positions = {vertex: j for layer in layers.values()
                 for j, vertex in enumerate(layer)}
    matrices = {}
    parity_cache = {}
    for degree, sources in layers.items():
        scalar, linear = [], []
        targets = layers.get(degree + 1, ())
        for source in sources:
            work()
            a = b = 0
            for target, value in scan.out[source].items():
                work()
                if (type(value) is not int or value <= 0
                        or value.bit_length() > 1 << variables):
                    raise ValueError("invalid first-jet dot polynomial")
                if scan.deg[target] != degree + 1:
                    raise ValueError("first-jet differential has invalid degree")
                if value not in parity_cache:
                    parity_cache[value] = _linear_parity(value, work)
                if value & 1:
                    a |= 1 << positions[target]
                if parity_cache[value]:
                    b |= 1 << positions[target]
            scalar.append(a)
            linear.append(b)
        matrices[degree] = scalar, linear, len(targets)

    if audit:
        for degree, (scalar, linear, _) in matrices.items():
            next_scalar, next_linear, _ = matrices.get(degree + 1, ([], [], 0))
            for a, b in zip(scalar, linear):
                work()
                if _apply(next_scalar, a, work):
                    raise ValueError("first-jet scalar differential does not square to zero")
                if _apply(next_scalar, b, work) ^ _apply(next_linear, a, work):
                    raise ValueError("first-jet differential violates AB + BA = 0")

    scalar_rank = dual_rank = 0
    for scalar, linear, target_count in matrices.values():
        scalar_rank += _rank(scalar, work)
        # The two source copies are streamed; no doubled matrix is retained.
        columns = (value for a, b in zip(scalar, linear)
                   for value in (a | (b << target_count), a << target_count))
        dual_rank += _rank(columns, work)
    total = len(group)
    t, kappa = total - 2 * scalar_rank, total - dual_rank
    if (t < 0 or not 0 <= kappa <= t or (t == 0) != (kappa == 0)):
        raise ArithmeticError("invalid bounded first-jet homology dimensions")
    kind = ('contractible' if not t else
            'matching-rank' if kappa == 1 else 'knot-multiplier')
    work()
    return dict(vertices=list(group), matching=matching, variables=variables,
                objects=total, scalar_rank=scalar_rank, dual_rank=dual_rank,
                t=t, kappa=kappa, kind=kind,
                all_classical_rank_equivalent=(kappa == 1),
                knot_completion_rank_multiplier=kappa,
                knot_completion_lower_bound=2 * kappa,
                first_jet_identities_checked=bool(audit),
                work_units=work.used)
