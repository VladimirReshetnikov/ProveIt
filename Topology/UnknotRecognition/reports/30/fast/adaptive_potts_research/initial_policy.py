"""Measured-work switch from an ordinary order to a certified separator order.

Easy queries finish without separator preparation. At a completed crossing,
64*n transitions trigger one preparation. An unchanged order continues the
same table. A changed order restarts once, charging all prior transitions to
the original allowance. A state-cap failure may also trigger the preparation.
The uncapped fixed-color scalar query remains poly(n) 2^O(sqrt(n)).
"""
from .ordering import best_scan_order, order_profile, validate_order
from .potts import _budget
from .potts_exact import PottsLimit, potts_exact, witness_from_exact
from .separator_order import width_bounded_scan_order


class _Reorder(Exception):
    def __init__(self, crossings, transitions, peak):
        self.completed_crossings = crossings
        self.transitions = transitions
        self.peak_states = peak


def adaptive_potts_exact(diagram, *, colors=6, max_states=4096, max_transitions=200_000,
                         order=None, check=lambda: None, statistics=None, shade=None):
    """Exact scalar result with an audited ordering policy and total work.

Result ``transitions`` counts BOTH attempts if reordered. ``peak_states`` is
the maximum of their peaks, not a memory bound. Local limits retain policy
statistics but no unfinished scalar result. A global check exception propagates.
"""
    _budget(max_states, 'max_states')
    _budget(max_transitions, 'max_transitions')
    if type(colors) is not int or colors < 5:
        raise ValueError('colors must be an integer at least 5')
    if shade is not None and (type(shade) is not int or shade not in (0, 1)):
        raise ValueError('shade must be 0, 1, or None')
    check()
    n = diagram.crossings
    if order is not None:
        order = validate_order(n, order)
    if n and (max_states == 0 or max_transitions == 0):
        raise PottsLimit('adaptive Potts filter budget is zero')
    if order is None:
        order = best_scan_order(diagram.pd, tries=max(1, min(n, 12)), check=check)
    policy = dict(mode='ordinary', trial_transitions=64*n, preparations=0,
                  restarts=0, discarded_transitions=0, discarded_crossings=0)
    if statistics is not None:
        statistics['ordering_policy'] = policy
    certificate = None

    def prepare():
        nonlocal certificate
        check()
        greedy = best_scan_order(diagram.pd, tries=max(1, min(n, 12)), check=check)
        candidate = min((order, greedy), key=lambda o: order_profile(diagram.pd, o))
        certificate = width_bounded_scan_order(diagram.pd, order=candidate, check=check)
        policy['preparations'] = 1
        if statistics is not None:
            statistics['order_certificate'] = certificate
        return certificate['order'] != order

    def stage_check(crossings, transitions, peak):
        if certificate is not None or transitions < policy['trial_transitions']:
            return
        # Do not pay preparation after consuming the entire scalar allowance.
        if max_transitions is not None and transitions >= max_transitions:
            return
        policy['trigger'] = 'measured-work'
        if prepare():
            raise _Reorder(crossings, transitions, peak)
        policy['mode'] = 'certified-continue'

    options = dict(colors=colors, max_states=max_states, check=check, shade=shade)
    prior_work = prior_peak = 0
    result = None
    try:
        result = potts_exact(diagram, order=order, max_transitions=max_transitions,
                             _stage_check=stage_check, **options)
    except (PottsLimit, _Reorder) as stop:
        prior_work, prior_peak = stop.transitions, stop.peak_states
        remaining = None if max_transitions is None else max_transitions-prior_work
        if isinstance(stop, PottsLimit):
            policy['spent_transitions'] = prior_work
            # A certified order that just hit a cap cannot improve by repetition.
            if certificate is not None or remaining == 0:
                raise
            policy['trigger'] = 'state-limit'
            if not prepare():
                policy['mode'] = 'certified-declined'
                raise
        policy.update(mode='certified-restart', restarts=1,
                      discarded_transitions=prior_work,
                      discarded_crossings=stop.completed_crossings)
    if result is None:
        # Exit the first exception handler before allocating the replacement
        # table, releasing its traceback and the abandoned evaluator locals.
        try:
            result = potts_exact(diagram, order=certificate['order'],
                                 max_transitions=remaining, **options)
        except PottsLimit as exhausted:
            policy['spent_transitions'] = prior_work+exhausted.transitions
            raise PottsLimit(str(exhausted), transitions=policy['spent_transitions'],
                             peak_states=max(prior_peak, exhausted.peak_states),
                             completed_crossings=exhausted.completed_crossings) from exhausted
    result['transitions'] += prior_work
    result['peak_states'] = max(prior_peak, result['peak_states'])
    policy['spent_transitions'] = result['transitions']
    result['ordering_policy'] = dict(policy)
    if certificate is not None:
        result['order_certificate'] = certificate
    if statistics is not None:
        statistics.update(result)
    return result


def adaptive_potts_obstruction(diagram, **options):
    return witness_from_exact(adaptive_potts_exact(diagram, **options),
                              kind='adaptive-potts-jones-exact-differs-from-unknot')
