"""Validated diagram entry point for the experimental disk-certified backend."""
from time import monotonic
from disk_frontier import diagram_graph, bipolar_order, validate_connected_cut_order, GeometryError
from radical_scan import RadicalScan


def component_count(pd):
    labels={x for c in pd for x in c}
    parent={x:x for x in labels}
    def root(x):
        while parent[x]!=x: x=parent[x]
        return x
    for a,b,c,d in pd:
        parent[root(a)]=root(c);parent[root(b)]=root(d)
    return len({root(x) for x in labels})


def certified_homology(pd, *, order=None, mode='adaptive', max_objects=None, seconds=None):
    pd=[tuple(c) for c in pd]
    if not pd:
        raise ValueError('an empty PD needs an explicit number of isolated circles')
    diagram_graph(pd)  # closes the geometry-provenance precondition before any scan
    if order is None:
        order=list(range(len(pd)))
        try:
            validate_connected_cut_order(pd,order);order_kind='input-certified'
        except GeometryError:
            try: order=bipolar_order(pd);order_kind='certified-bipolar'
            except GeometryError: order=list(range(len(pd)));order_kind='input-with-safe-fallback'
    else:
        order=list(order);order_kind='supplied-with-safe-fallback'
        if sorted(order)!=list(range(len(pd))):raise ValueError('order is not a permutation')
    if seconds is not None and seconds<0: raise ValueError('seconds must be nonnegative')
    deadline=None if seconds is None else monotonic()+seconds
    scan=RadicalScan(mode=mode,max_objects=max_objects,deadline=deadline,shape_cache=False)
    for j in order: scan.add_crossing(pd[j])
    ranks=scan.ranks_by_degree()
    return dict(rank=scan.total_rank(),raw_homological_ranks=ranks,components=component_count(pd),
                order=order,order_kind=order_kind,stats=scan.stats,
                radical_profiles=scan.radical_profiles)


def recognize_certified(pd, **kwargs):
    """Exact for validated nonempty one-component classical diagrams.

    This prototype does not include the repository's structural or polynomial
    prefilters. Resource exceptions propagate; they are never a verdict.
    """
    pd=[tuple(c) for c in pd]
    diagram_graph(pd)
    if not pd or component_count(pd)!=1:
        raise ValueError('recognition entry point requires a nonempty one-component PD')
    result=certified_homology(pd,**kwargs)
    if result['rank']<2:raise ArithmeticError('invalid unreduced knot rank')
    result['status']='UNKNOT' if result['rank']==2 else 'KNOTTED'
    return result
