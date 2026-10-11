"""Span-guided integral vertex changes with an independently replayed witness."""
from hashlib import sha256
import json

from .normal_cocycle import _Budget
from .normal_surface_geometry import _prepare
from .cocycle_transport import _integer_heights
from .cocycle_span import minimize_cocycle_span
from .cocycle_gauge_verify import verify_cocycle_gauge
from .cocycle_transport_verify import _shield_callback


@_shield_callback
def optimize_cocycle_gauge(triangulation,heights,*,max_work=None,check=lambda:None):
    budget=_Budget(check,max_work);prepared=_prepare(triangulation,budget.tick)
    h=_integer_heights(prepared,heights,budget.tick)
    vertices=[[prepared['vertex_roots'][4*t+j]for j in range(4)]for t in range(len(h))]
    result=minimize_cocycle_span(vertices,h,check=budget.tick)
    potential=dict(zip(result['certificate']['vertex_ids'],result['certificate']['potential']))
    # Component constants do not change the edge coboundary. Anchor each
    # source vertex component, so irrelevant offsets do not inflate proof
    # coefficients or obscure their bit-size accounting.
    parent={v:v for v in potential}
    def root(v):
        while parent[v]!=v:
            parent[v]=parent[parent[v]];v=parent[v]
        return v
    for vs in vertices:
        budget.tick()
        for v in vs[1:]:
            a,b=root(vs[0]),root(v)
            if a!=b:parent[max(a,b)]=min(a,b)
    anchored={v:potential[v]-potential[root(v)]for v in potential}
    potential=anchored
    shifted=[]
    for row,vs in zip(h,vertices):
        budget.tick();values=[x+potential[v]for x,v in zip(row,vs)]
        shifted.append([x-values[0]for x in values])
    if sum(max(row)-min(row)for row in shifted)>sum(max(row)-min(row)for row in h):
        raise ArithmeticError('vertex gauge optimizer increased the normal-disc span')
    proof=dict(schema='cocycle-vertex-gauge-v1',
        source_sha256=sha256(json.dumps(triangulation,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
        potential=[[v,potential[v]]for v in sorted(potential)],heights=shifted)
    if not verify_cocycle_gauge(triangulation,heights,proof,check=budget.tick):
        raise ArithmeticError('vertex gauge failed independent source replay')
    return dict(heights=shifted,certificate=proof,changed=shifted!=h,
        span_witness=dict(heights=h,coordinates=result['coordinates'],span_certificate=result['certificate']),
        stats=dict(result['stats'],work=budget.work))
