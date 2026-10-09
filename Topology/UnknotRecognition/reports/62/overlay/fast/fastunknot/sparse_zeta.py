"""Output-sensitive recovery of a nonnegative Boolean zeta transform (MIT-0).

The oracle must be exact: query(S) returns (sum_{T subset S} h(T), token),
where h is nonnegative integer-valued. A token is opaque proof provenance.
No sparsity bound is required. There are at most r*s queries for s terms.
"""
from .sparse_incidence_common import allowance


class RecoveryLimit(RuntimeError):
    """A caller-selected work allowance was exhausted; not a mathematical result."""


def recover_nonnegative_zeta(r: int, total: int, query, *, max_terms=None,
                             record_witness=False, check=None):
    """Recover all nonzero terms; exceptions from query/check propagate.

    Returns (terms, steps, statistics). No partial terms are returned on a
    work-limit exception. ``steps`` supplies dominating zero witnesses for an
    independent forward checker; it is not a replay of the search algorithm.
    """
    if type(r) is not int or r < 0 or type(total) is not int or total < 0:
        raise ValueError('r and total must be nonnegative literal integers')
    if type(record_witness) is not bool:
        raise ValueError('record_witness must be bool')
    allowance(max_terms, 'max_terms')
    poll = check if check is not None else lambda: None
    poll()
    full = (1 << r) - 1
    terms, steps = [], []
    removed = logical_queries = 0

    def known(mask):
        mass = 0
        for term, count in terms:
            poll()
            if term & mask == term:
                mass += count
        return mass

    while removed < total:
        poll()
        if max_terms is not None and len(terms) >= max_terms:
            raise RecoveryLimit('sparse term allowance exhausted')
        current, raw, support_ref = full, total, None
        zeros = []
        for bit in range(r):
            poll()
            candidate = current ^ (1 << bit)
            value, token = query(candidate)
            logical_queries += 1
            if type(value) is not int or not 0 <= value <= total:
                raise ArithmeticError('zeta oracle returned an impossible count')
            residual = value - known(candidate)
            if residual < 0:
                raise ArithmeticError('negative residual zeta count')
            if residual:
                current, raw, support_ref = candidate, value, token
            elif record_witness:
                zeros.append([bit, candidate, token])
        amount = raw - known(current)
        if not 0 < amount <= total - removed:
            raise ArithmeticError('inconsistent nonnegative zeta oracle')
        terms.append((current, amount))
        if record_witness:
            steps.append(dict(mask=current, count=amount,
                              support_ref=support_ref, zeros=zeros))
        removed += amount
    poll()
    return terms, steps, dict(logical_zeta_queries=logical_queries,
                              recovered_terms=len(terms))
