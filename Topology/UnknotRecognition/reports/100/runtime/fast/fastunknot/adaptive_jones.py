"""A polynomial-work faithful Potts prelude with a binary Jones fallback.

The default prelude spends at most 128*n transitions, including any internal
Potts reorder. A completed query supplies its exact answer; local exhaustion
switches once to spin, charging all discarded transitions to the caller's
original cap. With caps/deadlines disabled the general bit bound is
2^O(sqrt(n)). Jones polynomial identity remains inconclusive for recognition.
"""
from .faithful_jones import faithful_potts_exact
from .filters import FilterLimit
from .ordering import validate_order
from .potts import _budget
from .potts_exact import PottsLimit, witness_from_exact
from .spin_jones import SpinLimit, spin_jones_exact, witness_from_spin


class AdaptiveJonesLimit(FilterLimit):
    def __init__(self, message, *, transitions=0, peak_states=0, completed_crossings=0):
        super().__init__(message)
        self.transitions = transitions
        self.peak_states = peak_states
        self.completed_crossings = completed_crossings


def adaptive_jones_exact(diagram, *, max_states=4096, max_transitions=200_000,
                         order=None, check=lambda: None, statistics=None,
                         include_polynomial=False, potts_trial_transitions=None):
    """Faithful identity/full-polynomial query with one shared transition cap.

    None selects the default 128*n Potts trial; zero skips it. An explicitly
    larger trial has its own charged cost and is outside the default polynomial
    prelude guarantee. Completed separator certificates survive local limits.
    Raw winning scalars retain their backend's format; use the obstruction
    wrapper for JSON-safe evidence. Partial values are never published.
    """
    for value, name in ((max_states, 'max_states'), (max_transitions, 'max_transitions'),
                        (potts_trial_transitions, 'potts_trial_transitions')):
        _budget(value, name)
    if type(include_polynomial) is not bool:
        raise ValueError('include_polynomial must be boolean')
    check()
    n = diagram.crossings
    if order is not None:
        order = validate_order(n, order)
    if n and (max_states == 0 or max_transitions == 0):
        raise AdaptiveJonesLimit('adaptive Jones budget is zero')
    trial = 128*n if potts_trial_transitions is None else potts_trial_transitions
    if max_transitions is not None:
        trial = min(trial, max_transitions)
    policy = dict(algorithm='potts-then-spin-v1', trial_limit=trial,
                  mode='potts-trial' if trial or not n else 'spin-direct',
                  switches=0, discarded_transitions=0,
                  potts_transitions=0, spin_transitions=0, spent_transitions=0,
                  reused_order=False)
    if statistics is not None:
        statistics['backend_policy'] = policy
    stage_stats, result = {}, None
    prior_work = prior_peak = 0

    def retain_certificate():
        certificate = stage_stats.get('order_certificate')
        if certificate is not None and statistics is not None:
            statistics['order_certificate'] = certificate
        return certificate

    def finish(answer, backend):
        check()
        policy.update(mode=backend+'-complete', spent_transitions=answer['transitions'])
        answer['selected_backend'] = backend
        answer['backend_policy'] = dict(policy)
        if statistics is not None:
            statistics.update(answer)
        return answer

    if trial or not n:
        try:
            result = faithful_potts_exact(diagram, max_states=max_states,
                max_transitions=trial, order=order, check=check, statistics=stage_stats,
                include_polynomial=include_polynomial)
        except PottsLimit as stop:
            prior_work, prior_peak = stop.transitions, stop.peak_states
            policy.update(mode='spin-pending',
                          discarded_transitions=prior_work,
                          potts_transitions=prior_work, spent_transitions=prior_work,
                          potts_stop=str(stop), potts_completed_crossings=stop.completed_crossings)
            retain_certificate()
        else:
            policy['potts_transitions'] = result['transitions']
            return finish(result, 'potts')
    # Outside the exception handler: the abandoned table's traceback is released
    # before a replacement table is allocated. Retain only counters/certificates.
    remaining = None if max_transitions is None else max_transitions-prior_work
    if n and remaining == 0:
        policy['mode'] = 'exhausted-before-spin'
        raise AdaptiveJonesLimit('shared Jones transition budget exhausted before spin',
                                 transitions=prior_work, peak_states=prior_peak)
    certificate = retain_certificate()
    spin_order = order if certificate is None else certificate['order']
    policy['reused_order'] = certificate is not None
    policy['switches'] = int(policy['mode'] == 'spin-pending')
    policy['mode'] = 'spin-running'
    spin_stats = {}
    try:
        result = spin_jones_exact(diagram, max_states=max_states,
            max_transitions=remaining, order=spin_order, check=check,
            statistics=spin_stats, include_polynomial=include_polynomial,
            certify_order=certificate is None)
    except SpinLimit as stop:
        total = prior_work+stop.transitions
        policy.update(mode='spin-limited', spin_transitions=stop.transitions,
                      spent_transitions=total)
        if statistics is not None and 'order_certificate' in spin_stats:
            statistics['order_certificate'] = spin_stats['order_certificate']
        raise AdaptiveJonesLimit(str(stop), transitions=total,
            peak_states=max(prior_peak, stop.peak_states),
            completed_crossings=stop.completed_crossings) from stop
    if certificate is not None:
        result['order_certificate'] = certificate
    policy['spin_transitions'] = result['transitions']
    result['transitions'] += prior_work
    result['peak_states'] = max(prior_peak, result['peak_states'])
    return finish(result, 'spin')


def adaptive_jones_obstruction(diagram, **options):
    result = adaptive_jones_exact(diagram, **options)
    kind = 'adaptive-faithful-jones-polynomial-nontrivial'
    return (witness_from_spin(result, kind=kind) if result['selected_backend'] == 'spin'
            else witness_from_exact(result, kind=kind))
