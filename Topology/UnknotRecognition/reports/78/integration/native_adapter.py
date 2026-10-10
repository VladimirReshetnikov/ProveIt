"""Opt-in adapter for the inspected ProveIt private geometry interface.

Audit pin: 8188525b70033dcfe7c51ea5ae2c8723ad0c0198.
Native execution was NOT performed in the delivered environment.

With Topology/UnknotRecognition/fast and this package's src on PYTHONPATH,
call export_native_model(...) or optimize_native(...). This module does not
produce any of the maintained diagram-...-disc certificate formats.
"""
from span_excess import HeightModel, optimize_band, minimize_edge_then_span
from span_excess.model import Budget, noop


def export_native_model(triangulation, heights, minimum_span_certificate, *, check=noop):
    from fastunknot.normal_surface_geometry import _prepare
    from fastunknot.cocycle_euler import _euler_model
    from fastunknot.integer_codec import encoded_integer
    prepared = _prepare(triangulation, check)
    vertices, h, edges, _, initial = _euler_model(
        prepared, heights, minimum_span_certificate, check)
    labels = list(map(encoded_integer, minimum_span_certificate['vertex_ids']))
    index = {v:i for i,v in enumerate(labels)}
    lo, hi = [None]*len(vertices), [None]*len(vertices)
    for t,i,s,j in minimum_span_certificate['matching']:
        lo[t],hi[s] = i,j
    vs = tuple(tuple(index[v] for v in row) for row in vertices)
    optimum = sum(max(z+initial[v] for v,z in zip(row,hs))-
                  min(z+initial[v] for v,z in zip(row,hs)) for row,hs in zip(vs,h))
    model = HeightModel(len(labels),vs,tuple(map(tuple,h)),tuple(lo),tuple(hi),
                        optimum,tuple(initial),tuple(map(tuple,edges)))
    model.validate()
    return model, prepared


def optimize_native(triangulation, heights, minimum_span_certificate, *,
                    radius=1, lexicographic=False, max_work=5_000_000, check=noop):
    from fastunknot.normal_cocycle import local_coordinates
    from fastunknot.normal_surface_geometry import _coordinates
    budget=Budget(max_work,check)
    model, prepared=export_native_model(triangulation,heights,minimum_span_certificate,
                                       check=budget.tick)
    if lexicographic:
        arithmetic=minimize_edge_then_span(model,check=budget.tick)
        potential=arithmetic['potential']
        score2=arithmetic['score2']
    else:
        arithmetic=optimize_band(model,radius,check=budget.tick)
        if arithmetic['best'] is None:
            return {'status':'NO_CANDIDATE_IN_REQUESTED_BAND','knot_verdict':None,
                    'arithmetic':arithmetic,'work':budget.work}
        potential=arithmetic['best']['proof']['potential']
        score2=arithmetic['best']['score2']
    coordinates=[local_coordinates([h+potential[v] for v,h in zip(vs,hs)])
                 for vs,hs in zip(model.vertices,model.heights)]
    cells=_coordinates(prepared,coordinates,budget.tick)
    if 2*cells['euler_characteristic'] != score2:
        raise ArithmeticError('native normal cell count disagrees with the research objective')
    # Deliberately do not relabel this as a minimum-span witness. In particular,
    # do not send it to a checker whose connectedness proof assumes span=D_*.
    return {'status':'RESEARCH_CANDIDATE','knot_verdict':None,
            'coordinates':coordinates,'euler_characteristic':cells['euler_characteristic'],
            'model':model.to_dict(),'arithmetic':arithmetic,'work':budget.work,
            'next_required_step':'Independent source-bound disc/annulus verification'}
