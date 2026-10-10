"""Minimize Euler edge penalty, then span on its entire optimum face."""
from .normal_surface_geometry import _prepare,_coordinates
from .normal_cocycle import local_coordinates,_Budget
from .cocycle_euler_flow import _minimize_difference
from .cocycle_span_verify import verify_cocycle_span
from .integer_codec import encoded_integer
from .cocycle_lex_geometry import edge_model,span_network,span_value


def _lift(vertices,heights,potential,check):
    rows=[]
    for vs,hs in zip(vertices,heights):
        check();rows.append(local_coordinates([z+potential[v] for v,z in zip(vs,hs)]))
    return rows


def _prepared_minimize_edge_span(prepared,heights,minimum_span,check):
    labels,vertices,h,edges=edge_model(prepared,heights,check);n=len(labels)
    initial=[0]*n
    if minimum_span is not None:
        global_vertices=[[labels[v] for v in row] for row in vertices]
        if not verify_cocycle_span(global_vertices,h,minimum_span,check=check):
            raise ValueError('minimum-span reuse requires a valid source certificate')
        initial=[encoded_integer(v) for v in minimum_span['potential']]
    first=_minimize_difference(n,edges,[],initial,check)
    primary=first['certificate'];p=primary['potential']
    stats=dict(primary=first['stats'],secondary_network=True)
    reuse=False
    if minimum_span is not None:
        reuse=span_value(vertices,h,p,check)==encoded_integer(minimum_span['disc_count'])
    rows=_lift(vertices,h,p,check) if reuse else None
    if reuse:
        proof=dict(minimum_span,potential=list(p),coordinates=rows)
        if not verify_cocycle_span(global_vertices,h,proof,check=check):
            raise ArithmeticError('retargeted span dual failed independent replay')
        secondary=dict(kind='minimum-span',certificate=proof)
        stats.update(secondary_network=False,secondary=dict(augmentations=0,span_dual_reused=True))
    else:
        objective,constraints,initial=span_network(vertices,h,edges,primary['edge_flows'],p,check)
        second=_minimize_difference(len(initial),objective,constraints,initial,check)
        secondary=dict(kind='network',certificate=second['certificate']);stats['secondary']=second['stats']
        p=second['certificate']['potential'][:n]
        rows=_lift(vertices,h,p,check)
    analysed=_coordinates(prepared,rows,check)
    if 2*analysed['euler_characteristic']!=2*analysed['normal_disks']-primary['objective']:
        raise ArithmeticError('edge/span objective differs from source Euler count')
    certificate=dict(schema='normal-cocycle-edge-span-v1',vertex_ids=labels,primary=primary,
        secondary=secondary,normal_pieces=analysed['normal_disks'],euler_characteristic=analysed['euler_characteristic'])
    from .cocycle_lex_verify import _inspect_edge_span
    if _inspect_edge_span(prepared,h,certificate,check) is None:
        raise ArithmeticError('lexicographic arithmetic replay failed')
    return dict(coordinates=rows,potential=p,certificate=certificate,stats=stats,
        euler_characteristic=analysed['euler_characteristic'],normal_pieces=analysed['normal_disks'],
        trust='arithmetic optimum for supplied geometry; primitive source and topology require separate authentication')


def minimize_cocycle_edge_span(triangulation,heights,*,minimum_span=None,max_work=None,check=lambda:None):
    budget=_Budget(check,max_work);prepared=_prepare(triangulation,budget.tick)
    answer=_prepared_minimize_edge_span(prepared,heights,minimum_span,budget.tick)
    answer['stats']['work']=budget.work
    return answer
