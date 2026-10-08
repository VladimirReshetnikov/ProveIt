"""Complete one-multiplier and all-multiplier shear optimization."""
from __future__ import annotations
from dataclasses import dataclass
from hashlib import sha256
import json
from .slp import Grammar
from .histogram import profile,reference_profile,reduced_image
from .flow import solve_tension,verify_tension,Budget

@dataclass
class Optimization:
    certificate: dict
    grammar: Grammar
    roots: list[int]


def fingerprint(g: Grammar, roots: list[int]) -> str:
    return sha256(json.dumps(g.to_dict(roots),sort_keys=True,separators=(',',':')).encode()).hexdigest()

def optimize(g: Grammar, roots: list[int], generators: list[int]|None=None, *,
             balanced_fast_path: bool=True, forest_fast_path: bool=True, budget: Budget|None=None) -> Optimization:
    g.validate_roots(roots)
    seen=sorted({abs(g.rules[n][1]) for n in g.reachable(roots) if g.rules[n][0]=='t'})
    alive=seen if generators is None else sorted(generators)
    if len(set(alive))!=len(alive) or any(type(a) is not int or a<=0 for a in alive):
        raise ValueError('distinct positive generator IDs required')
    if not set(seen)<=set(alive): raise ValueError('word uses absent generator')
    records=[]; profiles={}; best=None
    shared_budget=budget or Budget()
    for a in alive:
        p=profile(g,roots,a); profiles[a]=p
        s=solve_tension(p.gaps,balanced_fast_path=balanced_fast_path,forest_fast_path=forest_fast_path,budget=shared_budget)
        row={'multiplier':a,'constant':p.constant,'value':p.constant+s.value,
             'potentials':[[v,z] for v,z in sorted(s.potentials.items())],
             'dual':[[u,v,e,s.dual[(u,v,e)]] for u,v,e in sorted(p.gaps)],
             'balanced':s.balanced,'method':s.method,'phases':s.phases,'repairs':s.repairs,'work':s.work}
        records.append(row)
        key=(row['value'],a)
        if best is None or key<best: best=key
    if best is None:
        out,new=g,roots[:]; selected=None; length=0
    else:
        length,selected=best; row=next(r for r in records if r['multiplier']==selected)
        out,new=reduced_image(g,roots,profiles[selected],dict(row['potentials']))
    cert={'version':1,'source_sha256':fingerprint(g,roots),'generators':alive,
          'initial_length':sum(g.meta[x].length for x in roots),
          'optimal_length':length,'selected_multiplier':selected,'solutions':records}
    return Optimization(cert,out,new)

def verify_optimization(g: Grammar, roots: list[int], cert: dict, *, check_binding: bool=True) -> bool:
    fields={'version','source_sha256','generators','initial_length','optimal_length',
            'selected_multiplier','solutions'}
    if set(cert)!=fields or type(cert['version']) is not int or cert['version']!=1:
        raise ValueError('unsupported certificate schema')
    if any(type(cert[k]) is not int for k in ('initial_length','optimal_length')):
        raise ValueError('non-integer objective')
    if cert['selected_multiplier'] is not None and type(cert['selected_multiplier']) is not int:
        raise ValueError('non-integer selected multiplier')
    if check_binding and cert['source_sha256']!=fingerprint(g,roots): raise ValueError('wrong source binding')
    alive=cert['generators']
    if not isinstance(alive,list) or alive!=sorted(set(alive)) or any(type(x) is not int or x<=0 for x in alive):
        raise ValueError('invalid generator list')
    seen={abs(g.rules[n][1]) for n in g.reachable(roots) if g.rules[n][0]=='t'}
    if not seen<=set(alive): raise ValueError('omitted source generator')
    if cert['initial_length']!=sum(g.meta[x].length for x in roots): raise ValueError('initial length')
    rows=cert['solutions']
    if not isinstance(rows,list) or len(rows)!=len(alive): raise ValueError('missing multiplier solution')
    best=None
    for a,row in zip(alive,rows):
        required={'multiplier','constant','value','potentials','dual','balanced','method','phases','repairs','work'}
        if set(row)!=required or type(row['multiplier']) is not int or row['multiplier']!=a:
            raise ValueError('invalid solution record')
        p=reference_profile(g,roots,a)
        zz=row['potentials']; ff=row['dual']
        if (not isinstance(zz,list) or any(not isinstance(v,list) or len(v)!=2 for v in zz)
            or not isinstance(ff,list) or any(not isinstance(v,list) or len(v)!=4 for v in ff)):
            raise ValueError('malformed witness')
        if any(type(v) is not int for pair in zz for v in pair) or any(type(v) is not int for pair in ff for v in pair):
            raise ValueError('non-integer witness')
        z=dict(zz); f={(u,v,e):w for u,v,e,w in ff}
        if len(z)!=len(zz) or len(f)!=len(ff): raise ValueError('duplicate witness entry')
        if type(row['value']) is not int or type(row['constant']) is not int or row['constant']!=p.constant:
            raise ValueError('invalid objective data')
        verify_tension(p.gaps,z,f,row['value']-p.constant)
        key=(row['value'],a)
        if best is None or key<best: best=key
    expected=(0,None) if best is None else best
    if (cert['optimal_length'],cert['selected_multiplier'])!=expected:
        raise ValueError('wrong global optimum or selected multiplier')
    return True

def replay_moves(cert: dict) -> list[dict]:
    """Translate the chosen shear into existing version-3+ Whitehead moves.

    The factors commute. These are automorphism records, not a complete knot
    certificate; the host verifier must still replay the whole presentation.
    """
    a=cert['selected_multiplier']
    if a is None: return []
    row=next(x for x in cert['solutions'] if x['multiplier']==a); result=[]
    for v,z in row['potentials']:
        if not z: continue
        multiplier=a if z>0 else -a; k=abs(z)
        move={'kind':'whitehead' if k==1 else 'whitehead_power',
              'multiplier':multiplier,'subset':sorted([multiplier,v])}
        if k>1: move['exponent']=k
        result.append(move)
    return result
