#!/usr/bin/env python3
"""A single oriented squared-error congruence recovers signed Pell pairs.

All required nonnegative semantic inputs are represented by explicit three-
square guards; principal Pell pairs and congruence quotients are unrestricted.
The new unbounded signed-cap proof is separate from these finite operations.
"""
from pathlib import Path
from copy import deepcopy
import argparse, json, re, sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor/signed'))
import build_signed as S
import terminal_elimination as E
from factor_horn import add,neg,V

def change_source(raw,meta):
    source=deepcopy(raw);source.pop('metrics',None)
    retained={v['name']:i for i,v in enumerate(source['variables'])}
    bygate={r['gate']:r for r in meta['rows'] if r['gate'] is not None}
    memo={};steps=[]
    def atom(a):
        if a[0]=='c':return {():a[1]} if a[1] else {}
        i=a[1];name=meta['variables'][i]['name']
        if name in retained:return V(retained[name])
        if i in memo:return memo[i]
        p=E.normalize(bygate[i]['terms']);rhs=E.candidate(p,i,False)
        if rhs is None:raise ValueError('semantic restoration not monic')
        result={}
        for mon,c in rhs.items():
            value={():c}
            for j in mon:value=E.multiply(value,atom(['v',j]))
            result=add(result,value)
        if E.degree(result)>1:raise ValueError('semantic port not affine')
        memo[i]=result;steps.append({'raw_variable':i,'name':name,
            'restoration':E.as_terms(result)})
        return result
    def square(p):return E.multiply(p,p)
    cc=meta['cap_certificate'];W=atom(meta['scale'][0]);A=atom(meta['scale'][1])
    all_atoms=sorted({tuple(p[key]) for p in meta['powers'] for key in ('base','exponent','output')}|
                     {tuple(p['n']) for p in meta['modular_requests']})
    frame_rhs=add({():2},*(square(atom(a)) for a in all_atoms))
    yc=atom(cc['cap']['pair'][1]);cap_slack=atom(cc['aggregate']['slack'])
    bound_rhs=add(W,{():1},cap_slack,*(square(atom(s['pair'][1])) for s in meta['seeds']))
    errors={}
    for s in meta['seeds']:
        x,y=map(atom,s['pair']);k=atom(s['exponent'])
        errors=add(errors,square(add(y,neg(k))),square(add(x,{():-1})))
    Q=atom(cc['residue']['quotient'])
    replacement={'shared.frame_definition':add(W,neg(frame_rhs)),
        'index_cap.all_indices_bound':add(yc,neg(bound_rhs)),
        'index_cap.squared_index_errors':add(errors,neg(E.multiply(add(A,{():-1}),Q)))}
    changes=[]
    for label,p in replacement.items():
        hits=[j for j,r in enumerate(source['residuals']) if r['label']==label]
        if len(hits)!=1:raise ValueError('missing unique source row')
        j=hits[0];old=source['residuals'][j]
        new=dict(old,terms=E.as_terms(p));source['residuals'][j]=new
        changes.append({'row':j,'old':old,'new':new})
    source['domain']='unrestricted integers'
    source['variant']+=':oriented_signed_cap'
    cert={'schema':'oriented_signed_cap_source_v1','changes':changes,
        'frame_atoms':[{'token':list(a),'affine':E.as_terms(atom(a))} for a in all_atoms],
        'semantic_affine_restorations':steps,
        'cap':{k:cc[k] for k in ('cap','aggregate','residue')},
        'W':E.as_terms(W),'A':E.as_terms(A),'cap_ordinate':E.as_terms(yc),
        'cap_slack':E.as_terms(cap_slack),'error_quotient':E.as_terms(Q),
        'seeds':[{'exponent':E.as_terms(atom(s['exponent'])),
                  'X':E.as_terms(atom(s['pair'][0])),'Y':E.as_terms(atom(s['pair'][1]))}
                  for s in meta['seeds']]}
    return source,cert

def generate(out,max_support=16,late_signs=False,affine_support=None):
    out=Path(out)
    if out.exists() and any(out.iterdir()):raise ValueError('output must be empty')
    raw=json.loads((HERE/'equation240/raw/equation.json').read_text())
    meta=json.loads((HERE/'equation240/raw/raw_audit_input.json').read_text())
    source,transform=change_source(raw,meta)
    names={v['name']:i for i,v in enumerate(source['variables'])}
    exempt_names={meta['variables'][a[1]]['name'] for s in meta['seeds'] for a in s['pair']}
    exempt_names|={meta['variables'][r['quotient'][1]]['name'] for r in meta['modular_requests']}
    exempt_names|={'pow'+str(i)+'.quotient' for i in range(len(meta['powers']))}
    exempt_names.add('index_cap.error_square_quotient')
    if late_signs:
        exempt_names|={meta['variables'][p['output'][1]]['name'] for p in meta['powers']}
        exempt_names|={n for n in names if re.fullmatch(r'base[0-9]+\.T',n)}
        exempt_names|={'modular.root_quotient','crt.index_quotient','crt.nonnegative_quotient'}
    need_missing=exempt_names-set(names)
    if need_missing:raise ValueError(('missing exempt coordinate',need_missing))
    exempt={names[n] for n in exempt_names}
    proof=S.inference(source,exempt,[])
    proof['exempt_names']=sorted(exempt_names)
    guarded=deepcopy(source)
    for v in proof['guard_indices']:
        a,b,c=range(len(guarded['variables']),len(guarded['variables'])+3)
        guarded['variables'] += [{'name':f'nonnegative.{v}.{s}','kind':'integer_guard'} for s in ('a','b','c')]
        guarded['residuals'].append({'label':f'nonnegative.{v}',
            'terms':E.as_terms({(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
    target,certificate,metrics=E.optimize(guarded,max_support=max_support,affine_support=affine_support)
    verification=E.verify(guarded,target,certificate)
    result=metrics|verification|{'guards':len(proof['guard_indices']),
        'signed_principal_pairs':len(meta['seeds']),'semantic_exempt_coordinates':len(exempt),
        'bound':'V=W+1+sum(Y_i^2)+s','pooled_error':'sum((Y_i-k_i)^2+(X_i-1)^2)',
        'late_signs':late_signs}
    out.mkdir(parents=True)
    for name,obj in [('mixed_source.json',source),('guarded.json',guarded),
        ('source_certificate.json',transform),('sign_certificate.json',proof),
        ('equation.json',target),('projection_certificate.json',certificate),
        ('expanded_polynomial.json',E.expand(target)),('METRICS.json',result)]:
        (out/name).write_bytes(E.canonical_bytes(obj))
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
    p.add_argument('--max-support',type=int,default=16)
    p.add_argument('--affine-support',type=int)
    p.add_argument('--late-signs',action='store_true');a=p.parse_args()
    print(json.dumps(generate(a.output,a.max_support,a.late_signs,a.affine_support),indent=2))
