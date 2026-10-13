"""One independently certified fixed-upward strict Pachner descent.

The supplied finite connected orientable torus-boundary source may have any
number of vertices. One epoch allows at most one total upward 2--3 move and
stops at a strictly smaller endpoint. An all-zero cochain makes the existing
source-bound transport machinery purely geometric; no disc or LP search runs.
"""
from hashlib import sha256
import json

from .normal_surface_geometry import _prepare
from .pachner_cover_search import find_pachner_descent
from .normal_pachner_descent_verify import verify_normal_pachner_descent


class _CallbackRaised(BaseException):
    def __init__(self, error):
        self.error = error
        self.traceback = error.__traceback__


def reduce_pachner_descent_once(triangulation, *, check=lambda: None):
    """Return REDUCED with a strict macro proof, or completely searched UNCHANGED.

    The fixed total upward allowance is one, and all legacy resource caps are
    removed. This is polynomial preprocessing, with at most three elementary
    moves in an accepted first descent. UNCHANGED means the bounded move family
    was exhausted; it is neither a minimum-triangulation nor a knot certificate.
    Caller callback exceptions preserve identity across all legacy catches.
    """
    def guarded():
        try:
            check()
        except BaseException as error:
            raise _CallbackRaised(error) from None

    try:
        return _reduce(triangulation, guarded)
    except _CallbackRaised as interruption:
        raise interruption.error.with_traceback(interruption.traceback) from None


def _reduce(triangulation, check):
    prepared = _prepare(triangulation, check)
    n = len(prepared['tetrahedra'])
    heights = [[0]*4 for _ in range(n)]
    result = find_pachner_descent(triangulation, heights, max_upward=1,
        max_region_size=None, method='sleep', max_nodes=None, max_regions=None,
        max_work=None, cover_backend='oracle', max_oracle_states=None, check=check)
    if result['status'] not in ('DESCENT_FOUND', 'COMPLETE_BOUNDED_DESCENT'):
        raise ArithmeticError('uncapped fixed-upward descent did not complete')
    stats = dict(initial_tetrahedra=n, remaining_tetrahedra=n,
        search_nodes=result['stats']['nodes'], search_work=result['stats']['aggregate_work'],
        macros=0, upward_moves=0, downward_moves=0, search_complete=False)
    if result['status'] == 'COMPLETE_BOUNDED_DESCENT':
        stats['search_complete'] = True
        check()
        return dict(status='UNCHANGED', reason='complete total-one-upward descent family exhausted',
                    stats=stats)
    certificate = result['certificate']
    # The independently replayed packet, not the search's descriptive summary,
    # authenticates every intermediate move and its zero cochain.
    successor = certificate['moves'][-1]['triangulation']
    packet = dict(schema='normal-pachner-descent-v1',
        source_sha256=sha256(json.dumps(triangulation, sort_keys=True,
            separators=(',', ':')).encode('utf-8')).hexdigest(),
        certificate=certificate, successor=successor)
    if not verify_normal_pachner_descent(triangulation, packet, check=check):
        raise ArithmeticError('fixed-upward strict descent failed independent replay')
    upward = sum(step['transport']['move']['schema'] == 'pachner-23-v1'
                 for step in certificate['moves'])
    downward = len(certificate['moves'])-upward
    stats.update(remaining_tetrahedra=n-1, macros=1,
                 upward_moves=upward, downward_moves=downward)
    check()
    return dict(status='REDUCED', certificate=packet, stats=stats)
