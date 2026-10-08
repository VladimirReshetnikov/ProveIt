"""Exact scalar Jones specialization with a certified square-root frontier.

Without optional resource caps, fixed-color evaluation takes poly(n) 2^O(sqrt(n))
bit operations. Equality with the unknot remains inconclusive for recognition.
"""
from .filters import FilterLimit
from .ordering import validate_order
from .potts import _budget
from .potts_exact import potts_exact, witness_from_exact
from .separator_order import width_bounded_scan_order


def separator_potts_exact(diagram, *, colors=6, max_states=4096, max_transitions=200_000,
                          order=None, check=lambda: None, statistics=None, shade=None):
    _budget(max_states, 'max_states')
    _budget(max_transitions, 'max_transitions')
    if type(colors) is not int or colors < 5:
        raise ValueError('colors must be an integer at least 5')
    if shade is not None and (type(shade) is not int or shade not in (0, 1)):
        raise ValueError('shade must be 0, 1, or None')
    check()
    if order is not None:
        order = validate_order(diagram.crossings, order)
    if diagram.crossings and (max_states == 0 or max_transitions == 0):
        raise FilterLimit('separator Potts filter budget is zero')
    certificate = width_bounded_scan_order(diagram.pd, order=order, check=check)
    # Publish only a fully verified hierarchy. A later scalar-budget decline
    # still leaves a valid order for the exact Khovanov fallback.
    if statistics is not None:
        statistics['order_certificate'] = certificate
    result = potts_exact(diagram, colors=colors, max_states=max_states,
                         max_transitions=max_transitions, order=certificate['order'],
                         check=check, statistics=statistics, shade=shade)
    result['order_certificate'] = certificate
    return result


def separator_potts_obstruction(diagram, **options):
    return witness_from_exact(separator_potts_exact(diagram, **options),
                              kind='separator-potts-jones-exact-differs-from-unknot')
