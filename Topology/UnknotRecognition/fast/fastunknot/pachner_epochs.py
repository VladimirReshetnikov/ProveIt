"""Positive diagram search through independently replayed strict descents.

The upward allowance is PER EPOCH. Each accepted epoch strictly decreases
tetrahedra, so there are at most the initial source size many restarts.
A bounded stationary source or resource cap is inconclusive for the knot.
"""
from copy import deepcopy

from .diagram import Diagram
from .diagram_exterior import diagram_exterior
from .boundary_shellings import shell_boundary
from .normal_cocycle import rank_one_cocycle_seed,_Budget,CocycleLimit,local_coordinates
from .cocycle_span import minimize_cocycle_span
from .normal_disk_kernel import normal_compressing_disk_count
from .normal_surface_geometry import NormalOrbitError,_prepare,_coordinates
from .normal_transport_verify import verify_transport_disk_certificate,verify_transport_annulus_certificate,_callback_safe_call
from .pachner_cover_search import find_pachner_descent
from .pachner_cover_verify import inspect_pachner_descent
from .cocycle_gauge import optimize_cocycle_gauge


def pachner_epoch_seed_decide(diagram,*,max_upward_per_epoch=1,max_epochs=None,
                             max_nodes=1000,max_work=2000000,max_cycles=None,
                             shellings=False,optimize=False,regauge_interval=0,annulus_caps=False,check=lambda:None):
    return _callback_safe_call(_decide,check,diagram,max_upward_per_epoch=max_upward_per_epoch,
        max_epochs=max_epochs,max_nodes=max_nodes,max_work=max_work,max_cycles=max_cycles,
        shellings=shellings,optimize=optimize,regauge_interval=regauge_interval,annulus_caps=annulus_caps)


def _decide(diagram,*,max_upward_per_epoch,max_epochs,max_nodes,max_work,max_cycles,
            shellings,optimize,regauge_interval,annulus_caps,check):
    if type(shellings)is not bool or type(optimize)is not bool or type(annulus_caps)is not bool:
        raise ValueError('shellings, optimize and annulus_caps must be bool')
    if type(max_upward_per_epoch)is not int or max_upward_per_epoch<0:
        raise ValueError('max_upward_per_epoch must be a nonnegative integer')
    if type(regauge_interval)is not int or regauge_interval<0:
        raise ValueError('regauge_interval must be a nonnegative integer')
    for name,value in (('max_epochs',max_epochs),('max_nodes',max_nodes),('max_cycles',max_cycles)):
        if value is not None and (type(value)is not int or value<0):
            raise ValueError(name+' must be a nonnegative integer or None')
    budget=_Budget(check,max_work)
    stats=dict(epochs=0,nodes=0,upward_moves=0,downward_moves=0,disc_queries=0,epoch_records=[],
        gauge_queries=0,gauge_changes=0,annulus_queries=0)
    scope=dict(max_upward_per_epoch=max_upward_per_epoch,max_epochs=max_epochs,
        regauge_interval=regauge_interval,
        annulus_caps=annulus_caps,
        meaning='upward events are bounded per strictly descending epoch, not over the whole chain')
    def miss(reason,status='INCONCLUSIVE'):
        return dict(status='INCONCLUSIVE',method='native-pachner-epochs',reason=reason,
            bounded_search_status=status,scope=scope,stats=stats,work=budget.work)
    try:
        source=Diagram.from_pd(diagram.pd);original=diagram_exterior(source,check=budget.tick)
        raw=original;shelling=None
        if shellings:
            shell=shell_boundary(raw,check=budget.tick);raw=shell['triangulation']
            shelling=dict(triangulation=raw,moves=shell['moves']);stats['shellings']=shell['stats']
        seed=rank_one_cocycle_seed(raw,check=budget.tick);h=seed['heights'];stats['seed']=seed['stats'];span_witness=None
        if optimize:
            result=minimize_cocycle_span(seed['vertices'],h,check=budget.tick)
            span_witness=dict(heights=deepcopy(h),coordinates=result['coordinates'],span_certificate=result['certificate'])
            potential=dict(zip(result['certificate']['vertex_ids'],result['certificate']['potential']))
            h=[[x+potential[v]for x,v in zip(row,vs)]for row,vs in zip(h,seed['vertices'])]
            stats['optimization']=result['stats']
        initial_h=deepcopy(h);initial_t=len(raw['tetrahedra']);steps=[]
        stats.update(initial_tetrahedra=initial_t,remaining_tetrahedra=initial_t)
        if max_nodes==0:return miss('Pachner node allowance exhausted')
        stats['nodes']=1
        while True:
            if annulus_caps and span_witness is not None:
                stats['annulus_queries']+=1
                analysed=_coordinates(_prepare(raw,budget.tick),span_witness['coordinates'],budget.tick)
                if analysed['euler_characteristic']==0:
                    surface=dict(schema='diagram-cocycle-annulus-v1',input_pd=[list(r)for r in source.pd],
                        triangulation=raw,**span_witness)
                    proof=dict(schema='diagram-transport-annulus-v1',input_pd=[list(r)for r in source.pd],
                        source_triangulation=original,shelling=shelling,source_heights=initial_h,
                        steps=steps,surface_certificate=surface)
                    if not verify_transport_annulus_certificate(source,proof,check=budget.tick):
                        raise ArithmeticError('epoch annulus cap failed independent source/connectivity replay')
                    return dict(status='UNKNOT',method='native-pachner-annulus',certificate=proof,
                        scope=scope,stats=stats,work=budget.work)
            budget.tick();coordinates=[]
            for row in h:
                budget.tick();coordinates.append(local_coordinates(row))
            query=normal_compressing_disk_count(raw,coordinates,max_cycles=max_cycles,
                record_certificate=True,check=budget.tick);stats['disc_queries']+=1
            if query['status']!='COMPLETE':return miss(query.get('reason','component query did not complete'))
            if query['contains_compressing_disk']:
                proof=dict(schema='diagram-transport-disc-v2'if stats['gauge_changes']else'diagram-transport-disc-v1',input_pd=[list(r)for r in source.pd],
                    source_triangulation=original,shelling=shelling,source_heights=initial_h,
                    steps=steps,coordinates=coordinates,disc_certificate=query['certificate'])
                if not verify_transport_disk_certificate(source,proof,check=budget.tick):
                    raise ArithmeticError('epoch diagram disc failed independent full-chain replay')
                return dict(status='UNKNOT',method='native-pachner-epochs',certificate=proof,
                    scope=scope,stats=stats,work=budget.work)
            if max_epochs is not None and stats['epochs']>=max_epochs:
                return miss('strict descent epoch allowance exhausted','EPOCH_LIMIT')
            remaining=None if max_nodes is None else max_nodes-stats['nodes']
            if remaining==0:return miss('Pachner node allowance exhausted')
            before=len(raw['tetrahedra'])
            descent=find_pachner_descent(raw,h,max_upward=max_upward_per_epoch,
                max_nodes=remaining,check=budget.tick)
            stats['nodes']+=descent['stats'].get('nodes',0)
            if descent['status']!='DESCENT_FOUND':
                return miss(descent.get('reason','the current source has no bounded-upward descent'),descent['status'])
            replay=inspect_pachner_descent(raw,h,descent['certificate'],
                max_upward=max_upward_per_epoch,check=budget.tick)
            if replay is None or len(replay['triangulation']['tetrahedra'])>=before:
                raise ArithmeticError('epoch did not independently replay a strict descent')
            steps.extend(descent['certificate']['moves']);raw=replay['triangulation'];h=replay['heights'];span_witness=None
            stats['epochs']+=1;stats['remaining_tetrahedra']=len(raw['tetrahedra'])
            stats['upward_moves']+=replay['upward_moves'];stats['downward_moves']+=replay['downward_moves']
            stats['epoch_records'].append(dict(before=before,after=len(raw['tetrahedra']),
                upward_moves=replay['upward_moves'],downward_moves=replay['downward_moves'],
                search_stats=descent['stats']))
            if regauge_interval and stats['epochs']%regauge_interval==0:
                gauged=optimize_cocycle_gauge(raw,h,check=budget.tick);stats['gauge_queries']+=1
                span_witness=gauged['span_witness']
                if gauged['changed']:
                    h=gauged['heights'];steps.append(dict(gauge=gauged['certificate']));stats['gauge_changes']+=1
            if stats['epochs']>initial_t:raise ArithmeticError('strict descent restart bound failed')
    except (CocycleLimit,NormalOrbitError)as error:
        return miss(str(error))
