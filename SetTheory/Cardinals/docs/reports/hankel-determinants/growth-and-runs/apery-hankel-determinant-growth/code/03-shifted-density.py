"""Edgar's Apéry density on the band 1/C < x < C, C = 17+12 sqrt(2).

Mathematical source: G. A. Edgar, The Apéry Numbers as a Stieltjes Moment
Sequence, arXiv:2005.10733v2, especially Proposition 23 and the right-endpoint
expansion in Proposition 25. https://arxiv.org/abs/2005.10733v2

This small implementation follows the continuation-sheet calculation in
V. Reshetnikov's ProveIt report, code/02-szego-density_constant.py (the
repository and inspected revision are identified in README.md). The source's
left band, endpoint cutoffs and Szegő-constant quadrature are not included.
Evaluations use mpmath at the caller's precision; they are not enclosures.
"""

import mpmath as mp


def endpoint():
    """Return C at the current mpmath precision."""
    return 17 + 12 * mp.sqrt(2)


def critical_shift():
    """The value s* for which (s/(s+2))^2 = C^(-2)."""
    return 2 / (endpoint() - 1)


def _hyper(z):
    return mp.hyp2f1(mp.mpf(1) / 3, mp.mpf(2) / 3, 1, z)


def density(x):
    """Return phi(x) for 1/C < x < C with the required continuation sheet.

    The reciprocal variable u = 1/x is used below. The added hypergeometric
    term when u > (7+3 sqrt(5))/2 selects the continued branch; omitting it
    gives incorrect values in part of the band used by the small shifts.
    """
    x = mp.mpf(x)
    C = endpoint()
    if not 1 / C < x < C:
        raise ValueError("This replay density requires 1/C < x < C.")
    u = 1 / x
    root = mp.j * mp.sqrt(34 * u - u * u - 1)
    mu2 = (3 - 3 * u - root) / (2 * (1 + u) ** 2)
    lam = (u**3 + 30 * u * u - 24 * u + 1
           - (u * u - 7 * u + 1) * root) / (2 * (1 + u) ** 3)
    value = _hyper(lam)
    if u > (7 + 3 * mp.sqrt(5)) / 2:
        value += mp.j * mp.sqrt(3) * _hyper(1 - lam)
    return -mp.im(mu2 * value**2 / x) / mp.pi


def right_endpoint_log_weight():
    """Limit log(C phi(C t)/sqrt(1-t)) as t increases to 1."""
    return mp.log(mp.sqrt(endpoint()) / (mp.power(2, mp.mpf(5) / 4) * mp.pi**2))
