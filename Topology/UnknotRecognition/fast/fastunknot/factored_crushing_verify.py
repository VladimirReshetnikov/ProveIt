"""Independent checker for visible-factor native crushing proofs.

No discovery, factor-production, or source-construction routine is called.
The public API accepts a conclusive certificate only; partial results never
constitute a verdict. The caller's callback exceptions retain their identity.
"""
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import verify_crushing_recognition


class _CallbackRaised(BaseException):
    def __init__(self, error):
        self.error = error
        self.traceback = error.__traceback__


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _pd_equal(actual, expected, check):
    if type(actual) is not list or len(actual) != len(expected):
        return False
    for row, wanted in zip(actual, expected):
        check()
        if (type(row) is not list or len(row) != 4 or
                any(type(x) is not int for x in row) or tuple(row) != tuple(wanted)):
            return False
    return True


def _checked_components(word, n, packet, check):
    """Replay alternating-edge connectivity and independent gap separation.

    This accepts the established gauss-interlacement-v1 certificate with
    canonical group ordering. It does not rerun interlacement discovery.
    """
    check()
    fields = {'algorithm', 'original_crossings', 'crossing_components',
              'interlacement_forest'}
    _require(type(packet) is dict and set(packet) == fields, 'factorization schema')
    _require(packet['algorithm'] == 'gauss-interlacement-v1', 'factorization algorithm')
    _require(type(packet['original_crossings']) is int and
             packet['original_crossings'] == n, 'crossing count')
    groups, forest = packet['crossing_components'], packet['interlacement_forest']
    _require(type(groups) is list and len(groups) <= n, 'component container')
    _require(type(forest) is list and len(forest) == n-len(groups), 'forest size')
    owner = [-1]*n
    least = -1
    for c, group in enumerate(groups):
        check()
        _require(type(group) is list and 0 < len(group) <= n, 'component shape')
        previous = -1
        for x in group:
            check()
            _require(type(x) is int and previous < x < n and owner[x] == -1,
                     'component partition or order')
            owner[x] = c
            previous = x
        _require(least < group[0], 'component order')
        least = group[0]
    _require(all(c >= 0 for c in owner), 'incomplete component partition')

    positions = [[] for _ in range(n)]
    for i, x in enumerate(word):
        check()
        positions[x].append(i)
    _require(len(word) == 2*n and all(len(p) == 2 for p in positions), 'source traversal')
    parent, sizes = list(range(n)), [1]*n

    def root(x):
        check()
        while parent[x] != x:
            check()
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for edge in forest:
        check()
        _require(type(edge) is list and len(edge) == 2 and
                 all(type(v) is int and 0 <= v < n for v in edge), 'forest endpoint')
        x, y = edge
        a, b = positions[x]
        c, d = positions[y]
        _require(a < c < b < d or c < a < d < b, 'nonalternating forest edge')
        rx, ry = root(x), root(y)
        _require(owner[x] == owner[y] and rx != ry, 'forest cycle or component crossing')
        if sizes[rx] < sizes[ry]:
            rx, ry = ry, rx
        parent[ry] = rx
        sizes[rx] += sizes[ry]
    for group in groups:
        r = root(group[0])
        for x in group:
            _require(root(x) == r, 'disconnected claimed component')

    # Between its first and last visit a component may be interrupted only
    # by a whole nested component. Connectivity plus this separation proves
    # that the supplied groups are exactly the interlacement components.
    visits, stack = [0]*len(groups), []
    for x in word:
        check()
        c = owner[x]
        if visits[c] == 0:
            stack.append(c)
        _require(stack and stack[-1] == c, 'distinct components interlace')
        visits[c] += 1
        if visits[c] == 2*len(groups[c]):
            stack.pop()
    _require(not stack, 'incomplete nesting')
    return groups, owner


def _factor_diagrams(source, factorization, check):
    """Rebuild children using cyclic consecutive visits, preserving slots."""
    check()
    walk = source.traversal()
    word = []
    for dart in walk:
        check()
        word.append(dart//4)
    groups, owner = _checked_components(word, source.crossings, factorization, check)
    # Established producer semantics: empty diagram is one empty child;
    # a single component retains the original PD's edge labels literally.
    if len(groups) <= 1:
        return [source]

    local = [-1]*source.crossings
    by_component = [[] for _ in groups]
    for group in groups:
        for i, x in enumerate(group):
            check()
            local[x] = i
    for dart in walk:
        check()
        by_component[owner[dart//4]].append(dart)
    result = []
    for group, visits in zip(groups, by_component):
        check()
        rows = [[None]*4 for _ in group]
        m = len(visits)
        _require(m == 2*len(group), 'child visit count')
        for incoming_edge, dart in enumerate(visits):
            check()
            x, slot = divmod(dart, 4)
            row = rows[local[x]]
            outgoing_slot = (slot+2) % 4
            _require(row[slot] is None and row[outgoing_slot] is None, 'repeated strand visit')
            row[slot] = incoming_edge
            row[outgoing_slot] = (incoming_edge+1) % m
        check()
        result.append(Diagram.from_pd(rows))
        check()
    return result


def verify_factored_crushing_recognition(diagram, certificate, *, check=lambda: None):
    """Verify an exact all-UNKNOT or one-KNOTTED visible-factor quorum.

    Malformed certificates return False. Every caller exception, including
    ValueError, KeyboardInterrupt and SystemExit, propagates unchanged.
    """
    def guarded():
        try:
            check()
        except BaseException as error:
            raise _CallbackRaised(error) from None
    try:
        return _verify(diagram, certificate, guarded)
    except _CallbackRaised as interruption:
        raise interruption.error.with_traceback(interruption.traceback) from None


def _verify(diagram, certificate, check):
    check()
    try:
        source = Diagram.from_pd(diagram.pd)
        check()
        fields = {'schema', 'status', 'input_pd', 'factorization', 'factor_pds', 'proofs'}
        if (type(certificate) is not dict or set(certificate) != fields or
                certificate['schema'] != 'diagram-factor-crushing-v1' or
                certificate['status'] not in ('UNKNOT', 'KNOTTED') or
                not _pd_equal(certificate['input_pd'], source.pd, check)):
            return False
        factors = _factor_diagrams(source, certificate['factorization'], check)
        pds = certificate['factor_pds']
        if type(pds) is not list or len(pds) != len(factors):
            return False
        for pd, child in zip(pds, factors):
            check()
            if not _pd_equal(pd, child.pd, check):
                return False
        proofs = certificate['proofs']
        if (type(proofs) is not list or
                len(proofs) != (len(factors) if certificate['status'] == 'UNKNOT' else 1)):
            return False
        for expected_index, proof in enumerate(proofs):
            check()
            if type(proof) is not dict or set(proof) != {'factor_index', 'certificate'}:
                return False
            index = proof['factor_index']
            if type(index) is not int or not 0 <= index < len(factors):
                return False
            if certificate['status'] == 'UNKNOT' and index != expected_index:
                return False
            child_proof = proof['certificate']
            if (type(child_proof) is not dict or
                    child_proof.get('status') != certificate['status'] or
                    not verify_crushing_recognition(factors[index], child_proof, check=check)):
                return False
        check()
        return True
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False
