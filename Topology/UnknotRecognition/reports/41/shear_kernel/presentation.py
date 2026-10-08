"""Certified bounded-shear-depth reduction of supplied group presentations.

Results concern an abstract presentation. A knot verdict additionally requires
independent provenance from a validated classical knot diagram.
"""
from __future__ import annotations
from math import gcd
from .slp import Grammar
from .optimize import optimize,verify_optimization
from .replay import reference_image

def pure_power_terminal(g: Grammar,roots: list[int],generators: list[int]) -> dict|None:
    g.validate_roots(roots)
    if (not isinstance(generators,(list,tuple)) or len(set(generators))!=len(generators)
            or any(type(a) is not int or a<=0 for a in generators)):
        raise ValueError('distinct positive generator IDs required')
    uniform={0:0}
    for n in g.reachable(roots):
        q=g.rules[n]
        if q[0]=='t': uniform[n]=q[1]
        elif q[0]=='p': uniform[n]=uniform[q[1]]
        else:
            a,b=q[1:]
            uniform[n]=uniform[a] if uniform[a] and uniform[a]==uniform[b] else 0
    orders={a:0 for a in generators}
    for root in roots:
        if not g.meta[root].length: continue
        x=uniform[root]
        if not x: return None
        if abs(x) not in orders: raise ValueError('absent generator')
        orders[abs(x)]=gcd(orders[abs(x)],g.meta[root].length)
    factors=[(a,d) for a,d in sorted(orders.items()) if d!=1]
    return {'orders':[[a,d] for a,d in sorted(orders.items())],
            'is_infinite_cyclic':len(factors)==1 and factors[0][1]==0,
            'nontrivial_factors':[[a,d] for a,d in factors]}

def reduce_presentation(g,roots,generators,*,max_phases=32,balanced_fast_path=True):
    if type(max_phases) is not int or max_phases<0: raise ValueError('invalid phase cap')
    certificates=[]; sizes=[]
    for phase in range(max_phases+1):
        sizes.append({'rules':len(g.reachable(roots)),'expanded_length':sum(g.meta[x].length for x in roots)})
        terminal=pure_power_terminal(g,roots,generators)
        if terminal is not None:
            return g,roots,{'status':'decided_presentation','steps':certificates,'terminal':terminal,'sizes':sizes}
        if phase==max_phases: break
        step=optimize(g,roots,generators,balanced_fast_path=balanced_fast_path)
        if step.certificate['optimal_length']>=step.certificate['initial_length']:
            return g,roots,{'status':'inconclusive_stall','steps':certificates,'terminal':None,'sizes':sizes}
        certificates.append(step.certificate); g,roots=step.grammar,step.roots
    return g,roots,{'status':'inconclusive_phase_cap','steps':certificates,'terminal':None,'sizes':sizes}

def verify_presentation_reduction(g,roots,generators,record):
    for index,cert in enumerate(record['steps']):
        if cert['generators']!=sorted(generators): raise ValueError('generator set changed')
        # Subsequent producer hashes bind a different, equivalent DAG layout.
        # Logical validity is checked against the independently replayed words.
        verify_optimization(g,roots,cert,check_binding=(index==0))
        if cert['optimal_length']>=cert['initial_length']: raise ValueError('non-shortening phase')
        a=cert['selected_multiplier']; row=next(x for x in cert['solutions'] if x['multiplier']==a)
        g,roots=reference_image(g,roots,a,dict(row['potentials']))
    terminal=pure_power_terminal(g,roots,generators)
    if record['status']=='decided_presentation':
        if terminal is None or record['terminal']!=terminal: raise ValueError('incorrect terminal group')
    elif record['status'] not in ('inconclusive_stall','inconclusive_phase_cap'):
        raise ValueError('unknown status')
    return True
