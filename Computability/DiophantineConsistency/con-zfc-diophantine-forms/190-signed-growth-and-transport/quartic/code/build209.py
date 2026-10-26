#!/usr/bin/env python3
"""Literal affine-horizon compilation and saturated coordinate scaling.

The horizon replacement is semantic and requires PROOF.md. All later changes
are exact polynomial substitutions with a certified integral inverse on zeros.
"""
from pathlib import Path
from collections import defaultdict
import argparse, copy, hashlib, json

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'source210/equation.json'

def canonical(o):
    return (json.dumps(o,sort_keys=True,separators=(',',':'))+'\n').encode()
def P(terms):
    r=defaultdict(int)
    for c,m in terms:r[tuple(sorted(m))]+=c
    return {m:c for m,c in r.items() if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def add(*ps):
    r=defaultdict(int)
    for p in ps:
        for m,c in p.items():r[m]+=c
    return {m:c for m,c in r.items() if c}
def scale(p,k):return {m:c*k for m,c in p.items() if c*k}
def mul(p,q):
    r=defaultdict(int)
    for a,c in p.items():
        for b,d in q.items():r[tuple(sorted(a+b))]+=c*d
    return {m:c for m,c in r.items() if c}
def subst(p,mapping):
    r={}
    for m,c in p.items():
        q={():c}
        for v in m:q=mul(q,mapping.get(v,{(v,):1}))
        r=add(r,q)
    return r
def degree(p):return max(map(len,p),default=-1)
def expand(eq):
    return add(*(mul(P(r['terms']),P(r['terms'])) for r in eq['residuals']))
def save(out,eq,certificate):
    out.mkdir(parents=True,exist_ok=True)
    pp=expand(eq)
    metrics={'variables':len(eq['variables']),'residuals':len(eq['residuals']),
      'degree':degree(pp),'monomials':len(pp),'coefficient_height':max(map(abs,pp.values())),
      'residual_height':max(abs(c) for r in eq['residuals'] for c,_ in r['terms']),
      'residual_terms':sum(len(r['terms']) for r in eq['residuals'])}
    for name,obj in [('equation.json',eq),('expanded_polynomial.json',{'schema':'sparse-polynomial-v1','variables':len(eq['variables']),'terms':terms(pp)}),('metrics.json',metrics),('certificate.json',certificate)]:
        (out/name).write_bytes(canonical(obj))
    lines=['Domain: all coordinates independently range over the integers.',f"P(x0,...,x{len(eq['variables'])-1}) = sum(Rj^2 for j=0,...,{len(eq['residuals'])-1}).",'']
    for j,r in enumerate(eq['residuals']):
        ss=[]
        for c,m in r['terms']:
            v='*'.join('x'+str(i) for i in m)
            a=abs(c)
            piece=(str(a) if a!=1 or not v else '')+('*' if a!=1 and v else '')+v
            ss.append((' - ' if c<0 else ' + ')+piece)
        s=''.join(ss).strip()
        if s.startswith('+ '):s=s[2:]
        lines.append(f'R{j} = {s}')
    (out/'residuals.txt').write_text('\n'.join(lines)+'\n')
    print(out.name,metrics,flush=True)
    return metrics

def build(source=SOURCE,output=ROOT.parent/'rebuilt',fscale=64):
    raw=source.read_bytes(); old=json.loads(raw)
    if hashlib.sha256(raw).hexdigest()!='20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a':
        raise ValueError('Unexpected principal210 source')
    if old['variables'][0]['name']!='t0' or old['variables'][2]['name']!='growth.F' or old['variables'][178]['name']!='cofinal.horizon_root':
        raise ValueError('Bad source bindings')
    if old['residuals'][125]['label']!='cofinal.horizon' or old['residuals'][149]['label']!='growth_pell.divisibility':
        raise ValueError('Bad source row bindings')
    if fscale<1 or fscale&(fscale-1) or (1<<20)%fscale:
        raise ValueError('Scale must divide2^20')
    affine=copy.deepcopy(old)
    affine['residuals'][125]['terms']=[[-2,[]],[1,[0]],[-4,[178]]]
    affine['schema']='conzfc-affine-horizon-source-v1'
    affine['variant']='source210_with_t_equals_2_plus_4z'
    affine['parent_equation_sha256']=hashlib.sha256(raw).hexdigest()
    affine['horizon']='2+4*z'
    output.mkdir(parents=True,exist_ok=True)
    (output/'source210_original.json').write_bytes(raw)
    (output/'source210_affine.json').write_bytes(canonical(affine))
    keep=[i for i in range(210) if i!=178]
    ren={i:j for j,i in enumerate(keep)}
    eq=copy.deepcopy(affine)
    eq['variables']=[copy.deepcopy(old['variables'][i]) for i in keep]
    eq['variables'][0]={'name':'horizon.z','kind':'unrestricted_horizon_parameter'}
    eq['variables'][2]={'name':'growth.F_div_'+str(fscale),'kind':'saturated_integer_coordinate'}
    eq['residuals']=[]
    changes=[]
    mapping={0:{():2,(0,):4},2:{(2,):fscale}}
    for j,row in enumerate(affine['residuals']):
        if j==125:continue
        p=subst(P(row['terms']),mapping)
        divider=fscale if j==149 else 1
        if any(c%divider for c in p.values()):raise ValueError('Nonintegral row normalization')
        p={m:c//divider for m,c in p.items()}
        if degree(p)>2:raise ValueError('Residual degree increased')
        if any(178 in m for m in p):raise ValueError('Removed root remains')
        p={tuple(ren[i] for i in m):c for m,c in p.items()}
        new=dict(row,terms=terms(p))
        eq['residuals'].append(new)
        if new['terms']!=row['terms']:changes.append({'old_row':j,'new_row':len(eq['residuals'])-1,'divisor':divider,'before':row['terms'],'after':new['terms']})
    used={v for r in eq['residuals'] for _,m in r['terms'] for v in m}
    if used!=set(range(209)):raise ValueError('Unused coordinate')
    eq['schema']='conzfc-affine-horizon-scaled-v1'
    eq['variant']='affine209_Fscale'+str(fscale)
    eq['parent_equation_sha256']=hashlib.sha256(canonical(affine)).hexdigest()
    eq['coordinate_interpretation']={'t':'2+4*x0','F':f'{fscale}*x2'}
    cert={'schema':'affine-and-saturated-scaling-certificate-v1',
      'semantic_source_change':{'old_row':125,'old_terms':old['residuals'][125]['terms'],'new_terms':affine['residuals'][125]['terms'],'proof_required':True},
      'old_source_sha256':hashlib.sha256(raw).hexdigest(),'affine_source_sha256':hashlib.sha256(canonical(affine)).hexdigest(),
      'removed_old_coordinate':178,'removed_old_row':125,
      'substitutions':{'old_t':terms(mapping[0]),'old_F':terms(mapping[2]),'old_horizon_root':[[1,[0]]]},
      'F_divisibility':{'growth_row':149,'power_of_two_dividing_F':20,'chosen_scale':fscale,'normalized_row':148},
      'old_to_new':[[i,j] for i,j in ren.items()], 'changed_rows':changes,
      'output_sha256':hashlib.sha256(canonical(eq)).hexdigest()}
    metrics=save(output/f'affine209_F{fscale}',eq,cert)
    return eq,metrics

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',type=Path,default=SOURCE);p.add_argument('--output',type=Path,default=ROOT.parent/'rebuilt');p.add_argument('--scale',type=int,default=64)
    a=p.parse_args();build(a.source,a.output,a.scale)
