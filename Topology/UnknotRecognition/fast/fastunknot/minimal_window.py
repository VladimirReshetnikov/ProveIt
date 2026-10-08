"""Cancel before upper truncation; certify the stronger nice-order size bound.

Unlike support-window allocation pruning, every extension is fully allocated
and minimized before degrees above upper+1 are removed. Returned ranks still
cover only the requested interval. Nice-order certification affects the bound,
not exactness. Input must be a validated classical knot Diagram.
"""
from collections import Counter
from dataclasses import asdict
from math import comb
from time import monotonic

from .geometry import ScanLimit
from .scan_fast import FastScan
from .ordering import best_scan_order
from .nice_order import certify, nice_order, OrderError
from .window_scan import validate_seconds


class BoundedCompositionCache:
    """Keep coefficient memoization within the quadratic storage accounting."""
    def _compose(self, key):
        if len(self.composed) >= 4096:
            self.composed.clear()
        return super()._compose(key)


def erase_above(scan, cutoff):
    """Brutal upper truncation after complete cancellation, with adjacency cleanup."""
    removed = 0
    for v, matching in enumerate(scan.mid):
        if matching is None or scan.deg[v] <= cutoff:
            continue
        for w in list(scan.out[v]):
            scan.inc[w].remove(v)
        for u in list(scan.inc[v]):
            scan.out[u].pop(v)
        scan.mid[v] = scan.out[v] = scan.inc[v] = None
        removed += 1
    scan.live -= removed
    return removed


def khovanov_minimal_window_auto(diagram, lower, upper, *, order=None, max_objects=None,
        seconds=None, check_d_squared=False, reduction='standard', composition='standard',
        composition_max_variables=18, mirror=True, trace=False):
    """Exact original-raw interval ranks; optional mirror and certified nice order.

    The implementation supports the current exhaustive and adaptive reducers.
    Full allocation (including the temporary next degree) is charged to caps.
    A failed nice-order certificate withdraws only the sharper size guarantee.
    """
    validate_seconds(seconds)
    if type(lower) is not int or type(upper) is not int or lower > upper:
        raise ValueError('lower and upper must be integers with lower <= upper')
    if max_objects is not None and (type(max_objects) is not int or max_objects < 0):
        raise ValueError('max_objects must be nonnegative or None')
    if reduction not in ('standard','residue','adaptive'):
        raise ValueError('invalid reduction')
    if composition not in ('standard','component','component-dense'):
        raise ValueError('invalid composition')
    if type(composition_max_variables) is not int or composition_max_variables < 0:
        raise ValueError('composition_max_variables must be nonnegative')
    deadline = None if seconds is None else monotonic()+seconds
    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit('minimal window time budget exhausted')
    check()
    n = diagram.crossings
    mirrored = bool(mirror and n-lower < upper)
    work = diagram.mirror() if mirrored else diagram
    a,b = (n-upper,n-lower) if mirrored else (lower,upper)
    if order is None:
        order = best_scan_order(work.pd, tries=min(n,12), check=check) if n else []
        cert = certify(work.pd,order,check=check)
        if not cert.nice and n > 1:
            try: cert = nice_order(work.pd,check=check)
            except OrderError: pass
    else:
        cert = certify(work.pd,order,check=check)
    check()
    order = list(cert.order)
    scan_type = FastScan
    if reduction != 'standard':
        from .residue import AdaptiveScan, ResidueScan
        scan_type = AdaptiveScan if reduction == 'adaptive' else ResidueScan
    scan_type = type("MinimalWindowScan", (BoundedCompositionCache,scan_type), {})
    scan = scan_type(max_objects=max_objects,deadline=deadline,shape_cache=False)
    if composition != 'standard':
        from .component_algebra import install_on_empty_scan
        install_on_empty_scan(scan, minimum_pairs=0 if composition=='component-dense' else 64,
                              method='fast' if composition=='component-dense' else 'auto',
                              dense_limit=composition_max_variables)
    stages=[]
    scan.stats.update(truncated_objects=0,max_retained_objects=0,binomial_stages_checked=0)
    for t,v in enumerate(order,1):
        # This calls exhaustive elimination before any degree is removed.
        scan.add_crossing(work.pd[v])
        scan.stats['truncated_objects'] += erase_above(scan,b+1)
        scan.stats['max_retained_objects'] = max(scan.stats['max_retained_objects'],scan.live)
        profile=Counter(scan.deg[v] for v,m in enumerate(scan.mid) if m is not None)
        if cert.nice:
            factor=2 if t==n else 1
            if any(h<0 or h>t or count>factor*comb(t,h) for h,count in profile.items()):
                raise ArithmeticError('certified nice-order binomial invariant failed')
            scan.stats['binomial_stages_checked'] += 1
        if check_d_squared: scan.check_d_squared()
        if trace:
            matching=Counter((scan.deg[v],scan.algebra.pairs[m]) for v,m in enumerate(scan.mid) if m is not None)
            stages.append(dict(processed=t,by_degree=dict(profile),
                matching_profile=[(h,m,c) for (h,m),c in sorted(matching.items())]))
    ranks=scan.ranks_by_degree() if n else {0:2}
    ranks={h:c for h,c in ranks.items() if a<=h<=b}
    if mirrored: ranks={n-h:c for h,c in ranks.items()}
    check()
    stats=dict(scan.stats);stats.update(scan.algebra.stats)
    result=dict(window_rank=sum(ranks.values()),by_degree=dict(sorted(ranks.items())),
        raw_lower=lower,raw_upper=upper,complete_rank=lower<=0 and upper>=n,
        order=order,stats=stats,stages=stages,reduction=reduction,composition=composition,
        strategy='cancel-before-truncate',nice_order=asdict(cert),
        binomial_bound_certified=cert.nice,
        orientation=dict(mirrored=mirrored,selection='minimum raw upper depth'),
        profile_degree_convention='mirror raw' if mirrored else 'original raw')
    if hasattr(scan.algebra,'kernel_stats'):result['composition_stats']=dict(scan.algebra.kernel_stats)
    return result
