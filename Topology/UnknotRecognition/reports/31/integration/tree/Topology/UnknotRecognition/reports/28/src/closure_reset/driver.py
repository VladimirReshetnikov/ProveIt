"""Optional FastScan adapter and a complete reset recognizer.
Import fastunknot from a real checkout, or the separately labelled retained
source-derived fixture for reproducible research tests.
"""
from __future__ import annotations
from time import monotonic
from .diagram import validate, splice, component_count
from .pure import inspect
from .jet import certify_jet


def recognize_pd(pd, *, max_objects=None, seconds=None, check_d_squared=False,
                 reset=True, frontier_test=True):
    from fastunknot.scan_fast import FastScan
    from fastunknot.geometry import ScanLimit
    if seconds is not None and (isinstance(seconds,bool) or not isinstance(seconds,(int,float))
                                or seconds<0 or seconds!=seconds or seconds==float('inf')):
        raise ValueError('seconds must be finite and nonnegative')
    if max_objects is not None and (type(max_objects) is not int or max_objects<0):
        raise ValueError('max_objects must be a nonnegative integer or None')
    pd=validate(pd,knot=True); current=pd
    deadline=None if seconds is None else monotonic()+seconds
    events=[]; peak=0; max_gap=0; total_scanned=0; parity_blocks=0; jet_blocks=0; resets=0
    def check():
        if deadline is not None and monotonic()>=deadline: raise ScanLimit('time budget exhausted')
    def finish(status,reason,**extra):
        return dict(status=status,reason=reason,rank_cap=2 if status=='UNKNOT' else (3 if status=='NONTRIVIAL' else None),
                    events=events,stats=dict(peak_objects=peak,max_gap=max_gap,scanned=total_scanned,
                    resets=resets,nonsingleton_pure_blocks=parity_blocks,nonsingleton_jet_blocks=jet_blocks),**extra)
    try:
        check()
        if not current: return finish('UNKNOT','crossingless circle')
        while current:
            check(); scan=FastScan(max_objects=max_objects,deadline=deadline,shape_cache=False)
            scan.hook=check; restarted=False
            for stage,crossing in enumerate(current,1):
                check(); scan.add_crossing(crossing); total_scanned+=1
                max_gap=max(max_gap,stage)
                peak=max(peak,scan.stats['max_objects_before_elimination'])
                if check_d_squared: scan.check_d_squared()
                if not scan.points:
                    if stage!=len(current): raise ArithmeticError('closed proper prefix of knot projection')
                    r=scan.total_rank()
                    if r<2 or r%2: raise ArithmeticError('invalid classical knot rank')
                    events.append(dict(type='terminal',stage=stage,rank=r))
                    return finish('UNKNOT' if r==2 else 'NONTRIVIAL','complete scalar closure',exact_terminal_rank=r)
                if not frontier_test: continue
                groups,data,_=inspect(scan)
                parity_blocks+=sum(d is not None and d.has_edge for d in data)
                jets=[certify_jet(scan,g) for g in groups]
                jet_blocks+=sum(j is not None and j.has_edge for j in jets)
                witnesses=[]; residuals={}; lower=0
                for pure,j in zip(data,jets):
                    bound=0 if pure is None else pure.lower_bound
                    record=dict(pure=None if pure is None else pure.as_dict())
                    if j is not None:
                        check()
                        if j.matching not in residuals:
                            residuals[j.matching]=splice(current[stage:],scan.algebra.pairs[j.matching])
                        residual=residuals[j.matching]; count=component_count(residual)
                        record.update(jet=j.as_dict(),completion_components=count,
                                      pairs=scan.algebra.pairs[j.matching])
                        if count==1:
                            bound=max(bound,2*j.kappa)
                        elif pure is not None:
                            bound=max(bound,4*pure.beta)
                    if bound:
                        record['lower_bound']=bound; witnesses.append(record); lower+=bound
                if lower>=4:
                    events.append(dict(type='closure-obstruction',stage=stage,lower_bound=lower,
                                       blocks=witnesses))
                    return finish('NONTRIVIAL','whole closure-summand rank obstruction',rank_lower_bound=lower)
                if reset and len(groups)==1 and jets[0] is not None:
                    j=jets[0]; residual=residuals[j.matching]
                    if component_count(residual)==1:
                        if j.kappa!=1: raise ArithmeticError('unresolved jet checkpoint violates dichotomy')
                        events.append(dict(type='reset',stage=stage,pairs=scan.algebra.pairs[j.matching],
                                           block=j.as_dict(),residual=residual))
                        current=residual; resets+=1; restarted=True; break
            if not restarted: raise ArithmeticError('scan did not close')
        raise ArithmeticError('unexpected empty residual')
    except ScanLimit as exc:
        return finish('UNKNOWN',str(exc))


def replay(pd,result, *, max_objects=None):
    """Deterministic replay recomputes the scanner; not a standalone proof kernel."""
    if result.get('status')=='UNKNOWN': raise ValueError('UNKNOWN is not a certificate')
    fresh=recognize_pd(pd,max_objects=max_objects,check_d_squared=True)
    import json
    if fresh['status']!=result.get('status') or json.dumps(fresh['events'],sort_keys=True)!=json.dumps(result.get('events'),sort_keys=True):
        raise ValueError('certificate replay mismatch')
    return True
