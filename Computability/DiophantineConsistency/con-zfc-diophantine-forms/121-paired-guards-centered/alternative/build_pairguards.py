#!/usr/bin/env python3
"""Replace paired sign guards by a product guard with proved positive sum.
Reads only frozen literal JSON plus bundled reviewed integer polynomial utilities.
"""
from pathlib import Path
from collections import Counter
import json,sys,copy,hashlib,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import terminal_elimination as E
import factor_horn as FH

def presemantic_certificate(eq,single_guards):
    """Literal ordered lower bounds; even powers need no sign assumption."""
    bounds={v:0 for v in single_guards};steps=[]
    def bound(poly):
        total=0;dependencies={}
        for m,c in poly.items():
            if not m:total+=c;continue
            if c<0:return None
            z=c
            for v,e in Counter(m).items():
                if v not in bounds:
                    if e%2:return None
                    z=0
                else:
                    dependencies[v]=bounds[v];z*=bounds[v]**e
            total+=z
        return total,dependencies
    while True:
        changed=False
        for rid,row in enumerate(eq['residuals']):
            p=E.normalize(row['terms'])
            for m,c in p.items():
                if len(m)!=1 or m[0] in bounds:continue
                v=m[0];rest=E.candidate(p,v,False)
                if rest is None:continue
                z=bound(rest)
                if z is None or z[0]<0:continue
                value=min(64,z[0]);bounds[v]=value;changed=True
                steps.append({'variable':v,'row':rid,'restoration':E.as_terms(rest),'lower_bound':value,'dependencies':[[i,n] for i,n in sorted(z[1].items())]})
        if not changed:break
    seeds=[]
    for rid,row in enumerate(eq['residuals']):
        if not row['label'].endswith('.index_at_most_Y'):continue
        p=E.normalize(row['terms']);names=eq['variables']
        ys=[m[0] for m,c in p.items() if len(m)==1 and c==1 and names[m[0]]['name'].endswith('.Y')]
        es=[m[0] for m,c in p.items() if len(m)==1 and c==-1 and names[m[0]]['name'].endswith('.YminusK')]
        if len(ys)!=1 or len(es)!=1:raise ValueError('seed row shape')
        y,e=ys[0],es[0]
        k={m:-c for m,c in p.items() if m not in [(y,),(e,)]}
        lower=bound(k)
        if lower is None or lower[0]<1:raise ValueError(('unproved positive seed',row['label']))
        seeds.append({'row':rid,'Y':y,'slack':e,'exponent':E.as_terms(k),'exponent_lower_bound':lower[0]})
    return {'schema':'literal_presemantic_lower_bounds_v1','guarded_leaves':sorted(single_guards),'steps':steps,'seed_indices':seeds,'conclusion':'Every seed exponent and Y ordinate is positive before power interpretation.'}

def build(source,out,squared_radius=False):
    mixed=json.loads((source/'mixed_source.json').read_text())
    domain=json.loads((source/'domain_certificate.json').read_text())
    original_source_hash=hashlib.sha256(E.canonical_bytes(mixed)).hexdigest()
    names={v['name']:i for i,v in enumerate(mixed['variables'])}
    pairs=[('choose'+str(i)+'.remainder','choose'+str(i)+'.rslack') for i in range(2)]
    pairs += [('range'+str(i)+'.remainder','range'+str(i)+'.slack') for i in range(10)]
    pairs=[(names[a],names[b]) for a,b in pairs]
    guarded_indices=set(domain['guard_indices'])
    radius_changes=[]
    if squared_radius:
        F=names['fact0.output'];F2=names['mul.36']
        for rid in (1,8,11):
            row=mixed['residuals'][rid]
            old=copy.deepcopy(row)
            new=E.substitute(E.normalize(row['terms']),F,{(F2,):1})
            row['terms']=E.as_terms(new)
            radius_changes.append({'row':rid,'old':old,'new':copy.deepcopy(row)})
        guarded_indices.remove(F)
        mixed['variant']+=':squared_factorial_carrier'

    covered={v for pair in pairs for v in pair}
    if not covered<=guarded_indices:raise ValueError('every pair needs original individual sign guards')
    cert=[]
    for a,b in pairs:
        candidates=[]
        for i,r in enumerate(mixed['residuals']):
            p=E.normalize(r['terms'])
            if p.get((a,))==-1 and p.get((b,))==-1 and p.get(())==-1:
                other={m:c for m,c in p.items() if m not in [(),(a,),(b,)]}
                if len(other)==1:
                    (m,c),=other.items()
                    if len(m)==1 and c==1 and mixed['variables'][m[0]]['name'].startswith('pow'):
                        candidates.append((i,m[0]))
        if len(candidates)!=1:raise ValueError(('no single power-sum row',a,b,candidates))
        row,power=candidates[0]
        cert.append({'left':a,'right':b,'sum_row':row,'positive_power_output':power,
                     'meaning':'left+right=positive_power_output-1>=0 after signed power bootstrap'})
    e=copy.deepcopy(mixed);e.pop('metrics',None);e['variant']+=':paired_sign_guards';e['domain']='unrestricted integers'
    for v in sorted(guarded_indices-covered):
        a,b,c=range(len(e['variables']),len(e['variables'])+3)
        e['variables'] += [{'name':f'nonnegative.{v}.{s}','kind':'integer_guard'} for s in ('a','b','c')]
        e['residuals'].append({'label':f'nonnegative.{v}','terms':E.as_terms({(v,):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})})
    for num,(l,r) in enumerate(pairs):
        a,b,c=range(len(e['variables']),len(e['variables'])+3)
        e['variables'] += [{'name':f'pairguard.{num}.{s}','kind':'integer_guard'} for s in ('a','b','c')]
        row={'label':f'pairguard.{num}','terms':E.as_terms({tuple(sorted((l,r))):1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})}
        e['residuals'].append(row);cert[num].update({'guard_variables':[a,b,c],'guard_row':len(e['residuals'])-1})
    presemantic=presemantic_certificate(mixed,guarded_indices-covered)
    factored,fc=FH.transform(e)
    final,pc,metrics=E.optimize(factored,max_support=16)
    receipt=E.verify(factored,final,pc)
    out.mkdir(parents=True,exist_ok=True)
    artifacts={'paired_source.json':e,'pair_certificate.json':{'schema':'nonnegative_pair_product_guards_v1','pairs':cert,'original_guard_indices':sorted(guarded_indices),'retained_single_guards':sorted(guarded_indices-covered),'source_sha256':hashlib.sha256(E.canonical_bytes(mixed)).hexdigest(),'bootstrap_reference':'PROOF.md','original_source_sha256':original_source_hash,'squared_factorial_carrier_changes':radius_changes},'presemantic_certificate.json':presemantic,'factored_source.json':factored,'factorization_certificate.json':fc,'equation.json':final,'projection_certificate.json':pc,'terminal_elimination_certificate.json':pc,'expanded_polynomial.json':E.expand(final),'METRICS.json':metrics|receipt|{'pair_guards':len(pairs),'single_guards':len(guarded_indices-covered)}}
    for n,v in artifacts.items():(out/n).write_bytes(E.canonical_bytes(v))
    print(json.dumps(artifacts['METRICS.json'],indent=2))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('output',type=Path);p.add_argument('--squared-radius',action='store_true');a=p.parse_args();build(a.source,a.output,a.squared_radius)
