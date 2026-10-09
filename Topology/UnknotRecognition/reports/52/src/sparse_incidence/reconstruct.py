"""Positive Boolean-zeta inversion without a dense Boolean cube.

The get_zeta callback MUST be the zeta transform of nonnegative weights.
Arithmetic consistency checks are not a substitute for this precondition.
"""
from .geometry import natural

class ResourceExhausted(RuntimeError):
    pass

def discover(rank, get_zeta, *, strategy='balanced', max_entries=None,
             check=lambda: None):
    natural(rank, 'rank')
    if strategy not in ('flat', 'balanced'):
        raise ValueError('strategy must be flat or balanced')
    if max_entries is not None:
        natural(max_entries, 'max_entries')
    full = (1 << rank)-1
    total = get_zeta(full)
    natural(total, 'total')
    empty = get_zeta(0)
    natural(empty, 'empty mass')
    if empty > total:
        raise ValueError('inconsistent zeta oracle')
    entries = [(0, empty)] if empty else []
    recovered = empty
    stats = {'residual_evaluations': 0, 'subset_tests': 0,
             'block_tests': 0, 'supports': 0}

    def residual(mask):
        check()
        stats['residual_evaluations'] += 1
        value = get_zeta(mask)
        natural(value, 'zeta value')
        for support, weight in entries:
            check()
            stats['subset_tests'] += 1
            if support & mask == support:
                value -= weight
        if value < 0:
            raise ValueError('negative residual: oracle is inconsistent')
        return value

    while recovered < total:
        check()
        if max_entries is not None and stats['supports'] >= max_entries:
            raise ResourceExhausted('support allowance exhausted')
        current = full
        if strategy == 'flat':
            blocks = [(i, i+1) for i in reversed(range(rank))]
        else:
            blocks = [(0, rank)] if rank else []
        while blocks:
            check()
            lo, hi = blocks.pop()
            block = ((1 << (hi-lo))-1) << lo
            candidate = current & ~block
            stats['block_tests'] += 1
            if residual(candidate) > 0:
                current = candidate
            elif strategy == 'balanced' and hi-lo > 1:
                mid = (lo+hi)//2
                blocks.extend(((mid, hi), (lo, mid)))
        weight = residual(current)
        if current == 0 or weight <= 0 or recovered + weight > total:
            raise ValueError('oracle violates positive-zeta invariant')
        entries.append((current, weight))
        recovered += weight
        stats['supports'] += 1
    entries.sort(key=lambda row: (row[0].bit_count(), row[0]))
    return dict(total=total, empty=empty, entries=entries, stats=stats)
