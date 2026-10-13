"""Complete streaming geometric first descent with at most one total expansion.

Every first strict descent has word D or UDD, where U is 2--3 and D is 3--2.
Enumerate those words directly, independently checking each local replacement.
No cochain, cover oracle, endpoint cache, normal search or retained attempt log
is used. The explicit source may have any number of finite vertices.
"""
from hashlib import sha256
import json

from .normal_surface_geometry import _prepare, _EDGES, NormalOrbitError
from .pachner23 import pachner_23
from .pachner32 import pachner_32
from .pachner23_verify import verify_pachner_23
from .pachner32_verify import verify_pachner_32
from .normal_geometric_descent_verify import verify_normal_geometric_descent


class _CallbackRaised(BaseException):
    def __init__(self, error):
        self.error = error
        self.traceback = error.__traceback__


def _downward_candidates(source, check):
    """One sorted local representative per eligible global interior edge."""
    prepared = _prepare(source, check)
    groups = {}
    for local, root in enumerate(prepared['edge_roots']):
        check()
        t, edge = divmod(local, 6)
        a, b = _EDGES[edge]
        groups.setdefault(root, []).append((t, a, b))
    candidates = []
    for root, occurrences in groups.items():
        check()
        if (root not in prepared['boundary_incidence'] and len(occurrences) == 3
                and len({t for t, _, _ in occurrences}) == 3):
            candidates.append(min(occurrences))
    # Preparation and incidence groups are local to this call, not retained
    # with all siblings or shared between different source triangulations.
    return sorted(candidates)


def _upward_candidates(source, check):
    """Retain both reciprocal orientations; no isomorphism quotient is used."""
    for t, row in enumerate(source['tetrahedra']):
        for face, paired in enumerate(row):
            check()
            if paired is not None and paired['tetrahedron'] != t:
                yield t, face


def reduce_geometric_descent_once(source, *, check=lambda: None):
    """Return REDUCED with a geometric proof, or exhaustively UNCHANGED.

    This fixed U=1 search is uncapped. Caller interruptions preserve identity;
    unexpected construction/replay failures cannot become an exhaustion claim.
    search_nodes counts the root and every verified U or UD prefix, excluding
    the terminal D/UDD endpoint. search_work counts all calls to the supplied
    callback, including preparation and final independent packet replay. These
    diagnostic units differ from the legacy cochain search's nodes/work.
    """
    def guarded():
        try:
            check()
        except BaseException as error:
            raise _CallbackRaised(error) from None
    try:
        return _reduce(source, guarded)
    except _CallbackRaised as interruption:
        raise interruption.error.with_traceback(interruption.traceback) from None


def _reduce(source, check):
    stats = dict(initial_tetrahedra=0, remaining_tetrahedra=0, search_nodes=0,
        search_work=0, macros=0, upward_moves=0, downward_moves=0,
        search_complete=False, upward_candidates=0, downward_candidates=0,
        upward_rejections=0, downward_rejections=0, downward_scans=0,
        verified_upward_candidates=0, verified_downward_candidates=0)

    def tick():
        stats['search_work'] += 1
        check()

    prepared = _prepare(source, tick)
    n = len(prepared['tetrahedra'])
    stats.update(initial_tetrahedra=n, remaining_tetrahedra=n, search_nodes=1)
    # Do not retain the initial prepared matching/incidence data across search.
    del prepared

    def downward(raw):
        stats['downward_scans'] += 1
        return _downward_candidates(raw, tick)

    def attempt(raw, upward, port):
        tick()
        direction = 'upward' if upward else 'downward'
        stats[direction+'_candidates'] += 1
        try:
            result = (pachner_23(raw, *port, check=tick) if upward else
                      pachner_32(raw, port[0], list(port[1:]), check=tick))
        except NormalOrbitError:
            # Eligibility filters do not replace formal-region checks. Guarded
            # caller exceptions are BaseException carriers and escape this catch.
            stats[direction+'_rejections'] += 1
            return None
        verifier = verify_pachner_23 if upward else verify_pachner_32
        if not verifier(raw, result['triangulation'], result['certificate'], check=tick):
            raise ArithmeticError('constructed Pachner candidate failed independent geometric replay')
        stats['verified_'+direction+'_candidates'] += 1
        return dict(triangulation=result['triangulation'], certificate=result['certificate'])

    def finish(steps):
        tick()
        packet = dict(schema='normal-geometric-descent-v1',
            source_sha256=sha256(json.dumps(source, sort_keys=True,
                separators=(',', ':')).encode('utf-8')).hexdigest(),
            steps=steps, successor=steps[-1]['triangulation'])
        if not verify_normal_geometric_descent(source, packet, check=tick):
            raise ArithmeticError('geometric first descent failed independent packet replay')
        upward = int(len(steps) == 3)
        stats.update(remaining_tetrahedra=n-1, macros=1,
                     upward_moves=upward, downward_moves=upward+1)
        tick()
        return dict(status='REDUCED', certificate=packet, stats=stats)

    for port in downward(source):
        step = attempt(source, False, port)
        if step is not None:
            return finish([step])
    for port in _upward_candidates(source, tick):
        up = attempt(source, True, port)
        if up is None:
            continue
        stats['search_nodes'] += 1
        after_up = up['triangulation']
        # All first contractions are necessary: taking only the first can miss
        # a different UD source on which a final contraction becomes available.
        for first_port in downward(after_up):
            first = attempt(after_up, False, first_port)
            if first is None:
                continue
            stats['search_nodes'] += 1
            after_first = first['triangulation']
            for final_port in downward(after_first):
                final = attempt(after_first, False, final_port)
                if final is not None:
                    return finish([up, first, final])
    stats['search_complete'] = True
    tick()
    return dict(status='UNCHANGED', reason='complete D and UDD geometric family exhausted', stats=stats)
