"""Compose causal amplification with cographic retention optimization.

This verifies an optimization model, not source geometry or knot triviality.
The caller must authenticate the common chamber graph and the fixed dependency
arena used to compare all candidate retention batches.
"""
from __future__ import annotations
from typing import Sequence
from cographic import Graph, maximum_batch
from causal import validate, amplification, path_bounds


def plan_reuse(vertices: int, edges: Sequence[tuple[int, int]],
               caps: Sequence[int], parents: Sequence[Sequence[int]],
               saved: Sequence[int], tasks: Sequence[int] | None = None,
               costs: Sequence[int] | None = None) -> dict:
    """Return a replayable minimum-upper-bound retention plan.

    Candidate edges map injectively to task slots. Unselected candidates start
    at the rebuild cap; selected candidates start at cap - saved progress.
    Noncandidate tasks start at their caps. All snapshots start valid.
    """
    validate(caps, parents)
    n=len(caps); k=len(edges)
    tasks=tuple(range(k) if tasks is None else tasks)
    if len(tasks)!=k or len(set(tasks))!=k or any(type(t) is not int or t<0 or t>=n for t in tasks):
        raise ValueError('candidate tasks must be distinct in-range task IDs')
    if len(saved)!=k or any(type(s) is not int or s<0 or s>caps[t] for s,t in zip(saved,tasks)):
        raise ValueError('one admissible saved-progress value per candidate required')
    costs=tuple([1]*n if costs is None else costs)
    a=amplification(caps,parents,costs)
    g=Graph(vertices,tuple(tuple(e) for e in edges),tuple(s*a[t] for s,t in zip(saved,tasks)))
    batch=maximum_batch(g)
    initial=list(caps)
    for e in batch['chosen']:
        initial[tasks[e]]-=saved[e]
    baseline=sum(p*b for p,b in zip(costs,path_bounds(caps,parents)))
    after=sum(p*b for p,b in zip(costs,path_bounds(caps,parents,initial)))
    return {'schema':'cographic-causal-reuse-v1',
            'scope':'relative-to-authenticated-geometry-and-fixed-dependencies',
            'caps':list(caps),'parents':[list(ps) for ps in parents],
            'event_costs':list(costs),'candidate_tasks':list(tasks),
            'saved_progress':list(saved),'amplification':list(a),'batch':batch,
            'initial_after_retention':initial,
            'baseline_work_bound':baseline,'retained_work_bound':after}
