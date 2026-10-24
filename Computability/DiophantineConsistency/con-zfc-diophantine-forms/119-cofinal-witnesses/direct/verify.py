#!/usr/bin/env python3
"""Independent exact verification of the 512-variable cofinal artifact.

Imports no builder, optimizer, CAS, repository module, or network client.
The unbounded soundness/completeness theorem is proved in PROOF.md.
"""
from pathlib import Path
from collections import Counter, defaultdict
from itertools import combinations_with_replacement
from math import factorial, isqrt
import argparse, hashlib, json

HERE=Path(__file__).resolve().parent

def require(test,message):
    if not test: raise ValueError(message)

def canonical(obj):
    return (json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()

def hash_json(obj):return hashlib.sha256(canonical(obj)).hexdigest()

def poly(row):
    p=Counter()
    for c,m in row['terms']:p[tuple(sorted(m))]+=c
    return {m:c for m,c in p.items() if c}

def expansion(e):
    coefficients=Counter()
    for r in e['residuals']:
        xs=sorted(poly(r).items())
        for a,b in combinations_with_replacement(range(len(xs)),2):
            ma,ca=xs[a];mb,cb=xs[b]
            coefficients[tuple(sorted(ma+mb))]+=(1 if a==b else 2)*ca*cb
    return [[c,list(m)] for m,c in sorted(coefficients.items()) if c]

def check_equation(parent,child,certificate,expanded):
    require(hash_json(parent)==certificate['source_sha256'],'parent hash')
    require(hash_json(child)==certificate['output_sha256'],'child hash')
    require(len(parent['variables'])==517 and len(parent['residuals'])==310,'parent dimensions')
    require(len(child['variables'])==512 and len(child['residuals'])==310,'child dimensions')
    require(parent['domain']==child['domain']=='unrestricted integers','unrestricted integer domain')
    removed=[329,330,343,344,345]
    retained=[v for v in range(517) if v not in removed]
    renaming={v:i for i,v in enumerate(retained)}
    require(certificate['removed_old_coordinates']==removed,'removed coordinate list')
    require(certificate['retained_old_coordinates']==retained,'retained coordinate list')
    require(child['variables']==[parent['variables'][v] for v in retained],'whole variable metadata')
    oldrows={247:{():-1,(0,):1,(328,328):-1,(329,329):-1,(330,):-1,(330,330):-1},
             249:{(3,):1,(334,334):-1,(335,335):-1,(336,):-1,(336,336):-1},
             252:{():-1,(2,):1,(3,):-1,(343,343):-1,(344,344):-1,(345,):-1,(345,345):-1}}
    newrows={247:{():-1,(0,):1,(328,328):-1},
             249:{():-1,(3,):1,(334,334):-1,(335,335):-1,(336,):-1,(336,336):-1},
             252:{():1,(2,):1,(3,):-3,(6,6):-1}}
    newlabels={247:'cofinal.horizon_square',249:'cofinal.factorial_positive',252:'cofinal.beta_modulus'}
    for rid,r in enumerate(parent['residuals']):
        p=poly(r)
        if rid in oldrows:require(p==oldrows[rid],'literal original special row')
        elif any(v in removed for m in p for v in m):raise ValueError('nonprivate removed guard coordinate')
        target=newrows.get(rid,p)
        expected={tuple(renaming[v] for v in m):c for m,c in target.items()}
        require(poly(child['residuals'][rid])==expected,'row transformation '+str(rid))
        require(child['residuals'][rid]['label']==newlabels.get(rid,r['label']),'row label '+str(rid))
        require(max(map(len,expected),default=0)<=2,'quadratic residual '+str(rid))
    require(expanded=={'schema':'sparse_integer_polynomial_v1','domain':'unrestricted integers',
                       'variables':512,'terms':expansion(child)},'every collected quartic coefficient')
    ts=expanded['terms'];metrics={'variables':512,'quadratic_rows':310,'exact_degree':max(len(m) for c,m in ts),
         'expanded_monomials':len(ts),'max_abs_expanded_coefficient':max(abs(c) for c,m in ts),
         'max_abs_row_coefficient':max(abs(c) for r in child['residuals'] for c,m in r['terms']),
         'variable_kinds':dict(Counter(v['kind'] for v in child['variables']))}
    require(metrics==child['metrics'],'all stored metrics')
    return metrics

def regression_checks():
    # These exact finite checks are regression evidence, not the theorem.
    guard_cases=0
    for F in range(1,80):
        for V in range(-40,41):
            y=V*V+3*F-1;r0=y-F-1
            require(r0==V*V+2*F-2 and r0>=0 and y>=2,'immediate guard recovery')
            guard_cases+=1
    cofinal_cases=0
    for s in range(9):
        t=16+s*s;F=factorial(t);base=F*t*t+1;V=base**t;y=V*V+3*F-1
        require(y%F==0,'factorial divisibility of deterministic beta parameter')
        require(y>V*V>=base**(t+1)>=(1+t*F)**(t+1),'complete accumulator bound')
        require(y>=F+1,'endpoint bound')
        cofinal_cases+=1
    # Simulate arbitrary pending products bounded by a proof tree's t steps.
    products=0
    for t in range(16,25):
        F=factorial(t);V=(F*t*t+1)**t;y=V*V+3*F-1
        for m in range(t+2):
            state=(1+t*F)**m
            require(state<=y,'worst pending product bound');products+=1
    return {'immediate_guard_cases':guard_cases,'cofinal_horizon_cases':cofinal_cases,'pending_product_cases':products}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path);args=ap.parse_args()
    read=lambda n:json.loads((HERE/n).read_text())
    parent,child,cert,exp=[read(n) for n in ['source517.json','equation512.json','specialization_certificate.json','polynomial512.json']]
    metrics=check_equation(parent,child,cert,exp)
    # Deliberate corruptions must be rejected by the independent verifier.
    bad=json.loads(json.dumps(child));bad['residuals'][252]['terms'][0][0]+=1
    try:check_equation(parent,bad,cert,exp)
    except ValueError:pass
    else:raise ValueError('modified equation accepted')
    badexp=json.loads(json.dumps(exp));badexp['terms'][0][0]+=1
    try:check_equation(parent,child,cert,badexp)
    except ValueError:pass
    else:raise ValueError('modified coefficient accepted')
    receipt={'status':'PASS','metrics':metrics,'finite_regressions':regression_checks(),
             'corruptions_rejected':2,'new_formal_proof_claimed':False,
             'scope':'Complete literal transformation, private guard support, dimensions, every quartic coefficient, regression inequalities; ordinary proof remains separate.'}
    if args.output:args.output.write_bytes(canonical(receipt))
    print(json.dumps(receipt,sort_keys=True))

if __name__=='__main__':main()
