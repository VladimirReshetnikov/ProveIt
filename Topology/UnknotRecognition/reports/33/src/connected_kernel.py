"""Connected initial-support enumeration for complete bounded RIII unlocking."""
from __future__ import annotations
from layered_search import SearchExhausted, Stats, find_layered
from dart_kernel import projection_graph, R3System

def connected_sets(adj, limit):
    """Unique nonempty connected vertex sets of size <=limit, polynomial stack.

    Canonical include/exclude enumeration, rooted at the least selected vertex.
    A set is emitted only on an include step (or once for its singleton root).
    """
    if type(limit) is not int or limit<0: raise ValueError("nonnegative integer limit required")
    if not limit: return
    n=len(adj)
    for root in range(n):
        initial=frozenset((root,))
        yield initial
        if limit==1: continue
        frontier=frozenset(v for v in adj[root] if v>root)
        # Task = (selected, frontier, permanently excluded).
        stack=[(initial,frontier,frozenset())]
        while stack:
            selected,frontier,excluded=stack.pop()
            if not frontier or len(selected)>=limit: continue
            v=min(frontier); rest=frontier-{v}
            stack.append((selected,rest,excluded|{v}))
            bigger=selected|{v}
            yield bigger
            added={w for w in adj[v] if w>root and w not in bigger and w not in excluded}
            stack.append((bigger,rest|added,excluded))

def kernel_unlock(initial, depth, *, check=None, max_trials=None, max_regions=None,
                  stats=None, region_mode="core"):
    """Complete single-exponential-parameter algorithm with caps disabled.

    region_mode="core" enumerates connected sets of <=3*depth+2 core crossings;
    "support" is the slower theoretical alternative using <=7*depth+6 crossings.
    Returns (witness, tested_regions). If no witness exists within depth, the
    first item is None, not a knottedness verdict. Any cap raises SearchExhausted.
    Crossing-free inputs have no crossing-decreasing terminal move.
    """
    if type(depth) is not int or depth<0: raise ValueError("invalid depth")
    if region_mode not in ("core","support"): raise ValueError("invalid region mode")
    if max_regions is not None and (type(max_regions) is not int or max_regions<0):
        raise ValueError("invalid region cap")
    system=R3System()
    if system.goal(initial) is not None:
        return find_layered(system,initial,0),0
    if depth==0: return None,0
    if check: check()
    # No legal first move means no nonempty RIII trace at any depth.
    # This is also a shortcut in the inspected production causal-search audit.
    if next(iter(system.actions(initial)),None) is None: return None,0
    stats=Stats() if stats is None else stats
    # Cores are only an admissibility parameter, never read/write footprints.
    # Every transition and commutation test still uses the full dart footprint.
    bound=3*depth+2 if region_mode=="core" else 7*depth+6
    regions=(iter((frozenset(range(initial.n)),)) if initial.n<=bound
             else connected_sets(projection_graph(initial),bound))
    count=0
    for region in regions:
        if check: check()
        if max_regions is not None and count>=max_regions:
            raise SearchExhausted("connected-region allowance exhausted")
        count+=1
        witness=find_layered(system,initial,depth,
             admissible=lambda a,R=region: all(d//4 in R for d in
                         (a.key if region_mode=="core" else a.footprint)),
             check=check,max_trials=max_trials,stats=stats)
        if witness is not None: return witness,count
    return None,count
