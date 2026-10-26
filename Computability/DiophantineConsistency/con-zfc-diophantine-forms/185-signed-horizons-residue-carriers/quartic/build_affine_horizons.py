#!/usr/bin/env python3
"""Emit fixed ordinary quartics with a signed affine cofinal horizon.

Every output coordinate ranges independently over Z.  No exponentiation is
part of an emitted equation; powers occur only in the semantic proof.
"""
from collections import defaultdict
from pathlib import Path
import copy, hashlib, json

ROOT=Path(__file__).resolve().parent
PINS={
    'p213':'9a16fcdcea6310c01236ce500f753034f4095c1956b488f9fd8325b1ceeb89c6',
    'p215':'8d919a1e5d6a802765b6d010c0140fb1d83c3d36d211b209b7a8d2fb3f3fb6f6',
}

def encoded(p):
    return [[c,list(m)] for m,c in sorted(p.items()) if c]

def dictionary(terms):
    p=defaultdict(int)
    for c,m in terms:p[tuple(sorted(m))]+=c
    return {m:c for m,c in p.items() if c}

def product(p,q):
    r=defaultdict(int)
    for a,c in p.items():
        for b,d in q.items():r[tuple(sorted(a+b))]+=c*d
    return {m:c for m,c in r.items() if c}

def add(*ps):
    r=defaultdict(int)
    for p in ps:
        for m,c in p.items():r[m]+=c
    return {m:c for m,c in r.items() if c}

def substitute_t(p,root,minimum):
    # old t=2*minimum*z+minimum; delete old coordinate0 and renumber.
    r={}
    for mon,c in p.items():
        q={():c}
        for i in mon:
            factor={():minimum,(root-1,):2*minimum} if i==0 else {(i-1,):1}
            q=product(q,factor)
        r=add(r,q)
    return r

def canonical(obj):return (json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()

def show(p):
    parts=[]
    for mon,c in sorted(p.items()):
        if not c:continue
        factors=[]
        for i in sorted(set(mon)):
            n=mon.count(i);factors.append(f'x{i}'+(f'^{n}' if n>1 else ''))
        a=abs(c);term='*'.join(([str(a)] if a!=1 or not mon else [])+factors)
        parts.append(('-' if c<0 else '+')+term)
    s=' '.join(parts)
    return (s[1:] if s.startswith('+') else s) or '0'

def build(source,name,minimum,quartic_multiplier=None,square_multiplier=1,deduplicate_squares=False):
    path=ROOT/source/'equation.json';raw=path.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=PINS[source]:raise ValueError('source hash')
    parent=json.loads(raw);vs=copy.deepcopy(parent['variables'])
    if vs[0]['name']!='t0':raise ValueError('t coordinate')
    roots=[i for i,v in enumerate(vs) if v['name']=='cofinal.horizon_root']
    if len(roots)!=1:raise ValueError('root coordinate')
    root=roots[0]
    hs=[i for i,r in enumerate(parent['residuals']) if r['label']=='cofinal.horizon']
    if len(hs)!=1:raise ValueError('horizon row')
    horizon=hs[0]
    old_minimum=16 if source=='p213' else 128
    expected={():-old_minimum,(0,):1,(root,root):-4}
    if dictionary(parent['residuals'][horizon]['terms'])!=expected:raise ValueError('old horizon')
    vs.pop(0);vs[root-1]['name']='cofinal.signed_progression_parameter'
    rows=[];mapping=[];growth_change=None;square_change=None
    for i,r in enumerate(parent['residuals']):
        if i==horizon:continue
        p=dictionary(r['terms'])
        if r['label']=='growth.t_squared' and square_multiplier!=1:
            ti=next(i for i,v in enumerate(parent['variables']) if v['name']=='growth.t_squared')
            if p!={(0,0):-1,(ti,):1}:raise ValueError('square row')
            p={(0,0):-square_multiplier,(ti,):1}
            square_change={'row':i,'old':r['terms'],'new':encoded(p)}
        if quartic_multiplier is not None and r['label']=='growth.index':
            ki=next(i for i,v in enumerate(parent['variables']) if v['name']=='growth.index')
            ti=next(i for i,v in enumerate(parent['variables']) if v['name']=='growth.t_squared')
            if p!={(ki,):1,(ti,ti):-1}:raise ValueError('growth row')
            p={(ki,):1,(ti,ti):-quartic_multiplier}
            growth_change={'row':i,'old':r['terms'],'new':encoded(p)}
        q=substitute_t(p,root,minimum)
        if max(map(len,q),default=0)>2:raise ValueError('nonquadratic residual')
        rows.append({'label':r['label'],'terms':encoded(q)})
        mapping.append([i,len(rows)-1])
    eq={'schema':'conzfc-affine-horizon-v1','domain':'unrestricted integers',
        'polynomial':'sum(square(row) for row in residuals)','variables':vs,'residuals':rows,
        'source_equation_sha256':PINS[source],
        'semantic_horizon':{'minimum_absolute_value':minimum,'step':2*minimum,
            'coordinate':root-1,'formula':f'{minimum}+{2*minimum}*x{root-1}'},
        'growth_rule':'F=t^(1048576*t)' if source=='p213' else f'F=t^({quartic_multiplier*square_multiplier**2}*t^4)',
        'note':'growth_rule is proof metadata, not an operation in the polynomial'}
    row_operations=[]
    if deduplicate_squares:
        si=next(i for i,r in enumerate(rows) if r['label']=='growth.t_squared')
        # These constants are the authenticated t^2 coefficients in the parent.
        for label,c in [('shared.frame_definition',-4),('cap.pooled_index_residue',2)]:
            if c%square_multiplier:raise ValueError('nonintegral row operation')
            target=next(i for i,r in enumerate(rows) if r['label']==label)
            multiplier=c//square_multiplier
            p=add(dictionary(rows[target]['terms']),{m:multiplier*d for m,d in dictionary(rows[si]['terms']).items()})
            rows[target]['terms']=encoded(p)
            row_operations.append({'target':target,'source':si,'multiplier':multiplier})
    polys=[dictionary(r['terms']) for r in rows]
    expanded=add(*(product(p,p) for p in polys))
    live={i for p in polys for mon in p for i in mon}
    if live!=set(range(len(vs))):raise ValueError('unused variable')
    metrics={'variables':len(vs),'residuals':len(rows),'degree':max(map(len,expanded)),
        'monomials':len(expanded),'coefficient_height':max(map(abs,expanded.values())),
        'residual_coefficient_height':max(abs(c) for p in polys for c in p.values()),
        'residual_monomials':sum(map(len,polys))}
    cert={'source':source,'source_sha256':PINS[source],'source_commit':'02a78a08603cbae248c19c23a75907c6c6bd6443',
        'semantic_horizon_replacement':{'row':horizon,'old':parent['residuals'][horizon]['terms'],
            'new':encoded({():-minimum,(0,):1,(root,):-2*minimum})},
        'growth_change':growth_change,'square_change':square_change,'row_operations':row_operations,
        'deleted_coordinate':0,'retained_parameter_old':root,
        'old_to_new_rows':mapping,'minimum':minimum,'growth_multiplier':quartic_multiplier,
        'square_multiplier':square_multiplier,
        'scope':'algebraic identity with the changed semantic source; no old/new zero-set bijection is claimed'}
    out=ROOT/'affine_horizons'/name;out.mkdir(parents=True,exist_ok=True)
    for file,obj in [('equation.json',eq),('expanded_polynomial.json',{'variables':len(vs),'terms':encoded(expanded)}),
        ('metrics.json',metrics),('certificate.json',cert)]:
        (out/file).write_bytes(canonical(obj))
    (out/'residuals.txt').write_text('Domain: all coordinates independently range over Z.\n'
        +f'P(x0,...,x{len(vs)-1}) = '+f'sum(Rj^2,j=0,...,{len(rows)-1}) = 0.\n\n'
        +'\n'.join(f'R{j} = {show(p)}' for j,p in enumerate(polys))+'\n')
    (out/'variables.tsv').write_text('index\tname\n'+''.join(f'{i}\t{v["name"]}\n' for i,v in enumerate(vs)))
    return metrics

if __name__=='__main__':
    result={}
    result['p212_minimum8']=build('p213','p212_minimum8',8)
    result['p214_scaled_square']=build('p215','p214_scaled_square',8,512,2,True)
    print(json.dumps(result,indent=2))
