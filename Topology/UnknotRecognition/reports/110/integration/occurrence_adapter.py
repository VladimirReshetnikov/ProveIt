"""Additive research adapter for authenticated sparse occurrence rows.

This returns a reduction plan, NEVER a knot or handlebody verdict. A caller
must reconstruct/authenticate counts and transport every surviving attaching
curve through the original geometric cancellation checker. No native imports.
"""
from pivotwidth import Instance,replay,StateLimitExceeded
from pivotwidth.preprocess import peel_then_optimize


def propose_occurrence_reduction(counts, weights=None, *, state_limit=100000, max_dense_cells=1000000):
    if not isinstance(counts,dict):raise ValueError('counts must be a dictionary')
    rows=sorted(counts)
    if any(type(r) is not int or r<0 or not isinstance(counts[r],dict) for r in rows):
        raise ValueError('invalid source row labels')
    columns=set()
    for r in rows:
        for c,x in counts[r].items():
            if type(c) is not int or c<0 or type(x) is not int or x<0:raise ValueError('invalid unsigned source occurrence')
            if x:columns.add(c)
    columns=sorted(columns)
    if len(rows)*len(columns)>max_dense_cells:
        return {'status':'INCONCLUSIVE','reason':'dense adapter size budget; no mathematical conclusion'}
    ci={c:j for j,c in enumerate(columns)};a=[[0]*len(columns) for r in rows]
    for i,r in enumerate(rows):
        for c,x in counts[r].items():
            if x:a[i][ci[c]]=x
    if weights is not None and set(weights)!=set(rows):raise ValueError('weight inventory must match source rows')
    ww=[1 if weights is None else weights[r] for r in rows]
    try:
        cert=peel_then_optimize(Instance.from_dense(a,ww),state_limit=state_limit)
    except StateLimitExceeded as exc:
        return {'status':'INCONCLUSIVE','reason':str(exc)}
    checked=replay(a,ww,cert)
    return {'status':'REDUCTION_PLAN','cancellations':[[rows[r],columns[c]] for r,c in checked['schedule']],
            'remaining_rows':[rows[r] for r in cert['deferred_rows']],
            'deferred_weight':cert['deferred_weight'],'matrix_certificate':cert,
            'row_labels':rows,'column_labels':columns,
            'scope':'abstract unsigned occurrence optimization; source geometry and ordered transport are external'}
