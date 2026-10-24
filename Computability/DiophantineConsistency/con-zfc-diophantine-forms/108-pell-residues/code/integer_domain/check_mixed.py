#!/usr/bin/env python3
"""Independent finite mixed-domain audit; no builder or search is imported.

This checks sign propagation, exact integer guards, coordinate eliminations,
and all collected coefficients. The unbounded signed-Pell and modular power
theorems are supplied separately as mathematical proofs.
"""
from collections import defaultdict
from copy import deepcopy
from pathlib import Path
import argparse, hashlib, json
from independent_polynomial import poly, verify_expansion
from verify_projection import verify as projection

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(obj):
    return hashlib.sha256((json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()).hexdigest()

def square(p):
    out=defaultdict(int)
    for m,c in p.items():
        for n,d in p.items():
            out[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in out.items() if c}

def shifted_polynomial(p, bounds):
    result=defaultdict(int)
    for mon,c in p.items():
        terms={():c}
        for v in mon:
            newer=defaultdict(int)
            for key,a in terms.items():
                newer[tuple(sorted(key+(v,)))]+=a
                if bounds[v]>0:newer[key]+=a*bounds[v]
            terms=dict(newer)
        for key,a in terms.items():result[key]+=a
    return {key:a for key,a in result.items() if a}

def certify_nonnegative(p,bounds,strict=False):
    shifted=shifted_polynomial(p,bounds)
    if all(a>0 for a in shifted.values()) and all(
        all(mon.count(v)%2==0 or bounds[v]>=0 for v in set(mon)) for mon in shifted):
        if not strict or shifted.get((),0)>0:return True
    if strict:return False
    # Independently recover a possible exact rational-free affine square.
    from math import isqrt
    diag=sorted((mon[0],a) for mon,a in p.items() if len(mon)==2 and mon[0]==mon[1] and a>0)
    if not diag:return not p
    v,a=diag[0];r=isqrt(a)
    if r*r!=a:return False
    root={(v,):r}
    for u in sorted({u for mon in p for u in mon}-{v}):
        c=p.get(tuple(sorted((u,v))),0)
        if c%(2*r):return False
        if c:root[(u,)]=c//(2*r)
    c=p.get((v,),0)
    if c%(2*r):return False
    if c:root[()]=c//(2*r)
    return square(root)==p

def domain(source, signed, certificate):
    require(source['domain']=='nonnegative integers','source domain')
    require(signed['domain']=='unrestricted integers','target domain')
    require(digest(source)==certificate['source_sha256'],'source digest')
    require(digest(signed)==certificate['guarded_sha256'],'guarded digest')
    n=len(source['variables']); m=len(source['residuals'])
    proof=certificate['positivity']; guards=certificate['guards']
    seeds=proof['guard_indices']; excluded=set(proof['temporarily_signed'])
    required=set(proof['required_nonnegative'])
    require(len(excluded)==len(proof['temporarily_signed']),'repeated excluded variable')
    require(required.isdisjoint(excluded) and required|excluded==set(range(n)),
            'mixed domain partition')
    require(set(seeds)<=required and len(seeds)==len(set(seeds)),'guard input set')
    require(signed['variables'][:n]==source['variables'],'source variable prefix')
    require(signed['residuals'][:m]==source['residuals'],'source residual prefix')
    require(len(signed['variables'])==n+3*len(guards),'integer guard variable count')
    require(len(signed['residuals'])==m+len(guards),'integer guard row count')
    require([g['variable'] for g in guards]==seeds,'guard coverage')
    for i,g in enumerate(guards):
        a,b,c=n+3*i,n+3*i+1,n+3*i+2;v=g['variable']
        require(g['auxiliary']==[a,b,c],'private guard coordinates')
        require(poly(signed['residuals'][m+i]['terms'])==
                {(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1},'guard identity')
    # Check that exactly the theorem-designated witness roles were freed.
    extra={'shared_index.Bquotient','modular.root_quotient',
           'endpoint.u0','moduli_product.quotient','crt.nonnegative_quotient'}
    qs=set(); signed_roles=set()
    for i,v in enumerate(source['variables']):
        name=v['name']
        if ((name.startswith('pow') and name.endswith('.quotient')) or
            (name.startswith('index') and name.endswith(('Squotient','Rquotient'))) or
            name.endswith('.modular_quotient') or name in extra):
            qs.add(i)
        if ((name.startswith('index') and name.endswith(('.S','.R'))) or
            name=='shared_index.U'):
            signed_roles.add(i)
    require(qs==set(certificate['quotient_indices']),'quotient role set')
    signed_roles|=qs; products=[]
    for rid,row in enumerate(source['residuals']):
        p=poly(row['terms'])
        if row['label']=='multiplication' and any(q in qs for mon in p for q in mon):
            outputs=[mon[0] for mon,c in p.items() if len(mon)==1 and c==1]
            require(len(outputs)==1,'quotient product definition')
            v=outputs[0]
            require(all(v not in mon for mon in p if mon!=(v,)),'product output isolation')
            signed_roles.add(v);products.append({'row':rid,'output':v})
    require(products==certificate['product_rows'],'quotient product ledger')
    require(signed_roles==excluded,'unexpected released domain')
    known=set(seeds)
    bounds=[0 if v in known else -1 for v in range(n)]
    for step in proof.get('bound_steps',[]):
        v=step['variable'];lower=step['lower_bound']
        require(v in required and lower in (0,1,2) and lower>bounds[v], 'new lower bound')
        row=poly(source['residuals'][step['row']]['terms'])
        require(all(mon.count(v)<=1 for mon in row),'nonlinear target in bound step')
        A=defaultdict(int);B=defaultdict(int)
        for mon,a in row.items():
            if v in mon:A[tuple(u for u in mon if u!=v)]+=a
            else:B[mon]-=a
        A={mon:a for mon,a in A.items() if a};B={mon:a for mon,a in B.items() if a}
        if A and all(a<0 for a in A.values()):A={mon:-a for mon,a in A.items()};B={mon:-a for mon,a in B.items()}
        require(A and certify_nonnegative(A,bounds,strict=True),'positive divisor proof')
        if lower==2:
            BA=defaultdict(int,B)
            for mon,a in A.items():BA[mon]-=a
            require(certify_nonnegative({mon:a for mon,a in BA.items() if a},bounds,strict=True), 'bound two proof')
        else:
            require(certify_nonnegative(B,bounds,strict=lower==1),'nonnegative numerator proof')
        bounds[v]=lower;known.add(v)
    if 'bounds' in proof:require(bounds==proof['bounds'],'final lower bounds')
    for step in proof['proof_steps']:
        v=step['variable'];c=step['coefficient'];rhs=poly(step['rhs'])
        require(type(c)is int and c>0 and v in required-known,'new sign inference')
        require(all(all(0<=u<n and u!=v for u in mon) for mon in rhs),'RHS support')
        expected={(v,):c}
        for mon,a in rhs.items():
            expected[mon]=expected.get(mon,0)-a
        expected={mon:a for mon,a in expected.items() if a}
        row=poly(source['residuals'][step['row']]['terms'])
        require(row==expected or row=={mon:-a for mon,a in expected.items()},'literal sign row')
        if step['kind']=='affine_square':
            root=poly(step['square_root'])
            require(all(len(mon)<=1 for mon in root),'root must be affine')
            require(square(root)==rhs,'affine square expansion')
        else:
            require(step['kind']=='positive_monomials','unknown sign rule')
            for mon,a in rhs.items():
                require(a>0,'monomial coefficient')
                require(all(mon.count(u)%2==0 or u in known for u in set(mon)),
                        'missing sign antecedent')
        known.add(v)
    require(known==required,'required signs not covered')
    return {'status':'PASS','source_variables':n,'integer_guards':len(guards),
            'ordinary_sign_inferences':len(proof['proof_steps']),
            'exact_bound_inferences':len(proof.get('bound_steps',[])),
            'temporarily_signed_coordinates':len(excluded),
            'quotient_coordinates':len(qs)}

def verify(directory):
    d=Path(directory)
    read=lambda name:json.loads((d/name).read_text())
    source=read('source.json');guarded=read('guarded.json');cert=read('domain_certificate.json')
    equation=read('equation.json');elim=read('elimination_certificate.json')
    answer={'status':'PASS','domain':domain(source,guarded,cert),
            'projection':projection(guarded,equation,elim),
            'expansion':verify_expansion(equation,read('expanded_polynomial.json'))}
    bad=deepcopy(cert)
    if bad['positivity'].get('bound_steps'):
        bad['positivity']['bound_steps'][0]['lower_bound']=3
    else:bad['positivity']['proof_steps'][0]['rhs'][0][0]+=1
    try:domain(source,guarded,bad)
    except ValueError:answer['corrupt_sign_rejected']=True
    else:raise ValueError('accepted corrupt sign certificate')
    bad=deepcopy(elim);bad['steps'][0]['restoration'][0][0]+=1
    try:projection(guarded,equation,bad)
    except ValueError:answer['corrupt_projection_rejected']=True
    else:raise ValueError('accepted corrupt coordinate projection')
    bad=deepcopy(cert);bad['positivity']['temporarily_signed'].append(0)
    try:domain(source,guarded,bad)
    except ValueError:answer['extra_signed_role_rejected']=True
    else:raise ValueError('accepted extra signed witness')
    answer['scope']='Finite domain partition, polynomial identities and inverse projection. Semantic Pell/modular restoration is proved in the accompanying article.'
    return answer

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory',type=Path);p.add_argument('--receipt',type=Path)
    a=p.parse_args();r=verify(a.directory);text=json.dumps(r,indent=2,sort_keys=True)+'\n'
    if a.receipt:a.receipt.write_text(text)
    print(text)
