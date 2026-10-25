#!/usr/bin/env python3
"""Replace signed interval certificates by grouped symmetric residue caps."""
from pathlib import Path
import argparse, copy, hashlib, json
import terminal_elimination as E
import factor_horn as F
import translate_coordinates as T

def read(p):
    return json.loads(p.read_text())

def put(d,n,obj):
    d.mkdir(parents=True,exist_ok=True)
    (d/n).write_bytes(E.canonical_bytes(obj))

def sha(obj):
    return hashlib.sha256(E.canonical_bytes(obj)).hexdigest()

def transform(parent,merge='none'):
    eq = read(parent/'guarded.json')
    cert = read(parent/'transform_certificate.json')
    new = copy.deepcopy(eq)
    groups={}
    removed=[]
    for g in cert['guards']:
        if g['kind']!='postsemantic_interval':
            continue
        r,s=g['pair']
        p=E.normalize(eq['residuals'][g['bound_row']]['terms'])
        expected={():-1,(r,):-1,(s,):-1}
        residue={m:c-expected.get(m,0) for m,c in p.items()}
        residue={m:c for m,c in residue.items() if c}
        if len(residue)!=1:
            raise ValueError(('bound',g,residue))
        (m,c),=residue.items()
        if len(m)!=1 or c!=1:
            raise ValueError(('denominator',m,c))
        denom=m[0]
        groups.setdefault(denom,[]).append(r)
        removed.extend([g['row'],g['bound_row']])
    if sorted(len(v) for v in groups.values())!=[2,2,2,5]:
        raise ValueError(('groups',groups))
    new['residuals']=[r for i,r in enumerate(eq['residuals']) if i not in removed]
    changes=[]
    weighted=[]
    merge_record=None
    names={v['name']:i for i,v in enumerate(eq['variables'])}
    if merge!='none':
        small=names['pow4.output'];large=names['pow6.output'];q=names['pow2.output']
        small_rs=groups.pop(small)
        if merge=='products':
            for ri,r in enumerate(small_rs):
                w=len(new['variables'])
                new['variables'].append({'name':f'residue_pool.scaled{ri}','kind':'gate'})
                row={'label':f'residue_pool.scale{ri}','terms':E.as_terms({(w,):1,tuple(sorted((q,r))):-1})}
                new['residuals'].append(row)
                weighted.append({'variable':w,'radix':q,'remainder':r,'row':len(new['residuals'])-1})
                groups[large].append(w)
            merge_record={'method':merge,'small_denominator':small,'large_denominator':large,'radix':q,'small_remainders':small_rs,'scaled':weighted}
        elif merge=='aggregate':
            qsq=names['mul.520']
            target={(qsq,):1,(q,q):-1}
            if not any(E.normalize(r['terms'])==target for r in new['residuals']):
                raise ValueError('existing q-square definition missing')
            ss=len(new['variables'])
            new['variables'].append({'name':'residue_pool.small_squares','kind':'gate'})
            p={(ss,):1}
            for r in small_rs:p[(r,r)]=-1
            new['residuals'].append({'label':'residue_pool.small_squares','terms':E.as_terms(p)})
            merge_record={'method':merge,'small_denominator':small,'large_denominator':large,'radix':q,'radix_square':qsq,'small_remainders':small_rs,'sum_square':ss,'sum_row':len(new['residuals'])-1}
        else:raise ValueError(merge)
    for gi,(denom,remainders) in enumerate(groups.items()):
        a,b,c=range(len(new['variables']),len(new['variables'])+3)
        new['variables'] += [{'name':f'residue_pool{gi}.{s}','kind':'integer_guard'} for s in ('a','b','c')]
        p={(denom,denom):1,():-1,(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}
        for r in remainders:
            p[(r,r)]=-2
        if merge=='aggregate' and denom==merge_record['large_denominator']:
            p[tuple(sorted((merge_record['radix_square'],merge_record['sum_square'])))]=-2
        new['residuals'].append({'label':f'residue_pool.{gi}','terms':E.as_terms(p)})
        changes.append({'denominator':denom,'remainders':remainders,'auxiliary':[a,b,c],'row':len(new['residuals'])-1})
    new['variant'] += ':symmetric_residue_pools'
    record={'schema':'symmetric_residue_pool_v1','parent_guarded_sha256':sha(eq),'parent_transform_sha256':sha(cert),'removed_rows':sorted(removed),'removed_row_values':[eq['residuals'][i] for i in sorted(removed)],'groups':changes,'merge':merge_record,'new_source_sha256':sha(new)}
    return new,record

def build(parent,out,cap=16,merge='none'):
    new,record=transform(parent,merge)
    factored,fc=F.transform(new)
    projected,pc,metrics=E.optimize(factored,max_support=cap)
    receipt=E.verify(factored,projected,pc)
    shifts={i:-1 for i,v in enumerate(projected['variables']) if v['name'].startswith('crt.encoded') or v['name'].endswith('minus1')}
    for i,v in enumerate(projected['variables']):
        if v['name']=='t0':shifts[i]=-16
    final=T.translate(projected,shifts)
    poly=E.expand(final)
    met={'variables':len(final['variables']),'rows':len(final['residuals']),'degree':max(len(m) for c,m in poly['terms']),'monomials':len(poly['terms']),'height':max(abs(c) for c,m in poly['terms']),'row_height':max(abs(c) for r in final['residuals'] for c,m in r['terms']),'residue_groups':len(record['groups']),'residue_count':11,'merge':merge}
    trans={'schema':'integral_translation_v1','input_sha256':sha(projected),'output_sha256':sha(final),'shifts':[[i,s] for i,s in shifts.items()],'convention':'old=new+shift'}
    for n,o in [('source.json',new),('pool_certificate.json',record),('factored_source.json',factored),('factorization_certificate.json',fc),('projected.json',projected),('projection_certificate.json',pc),('PROJECTION_CHECK.json',receipt),('translation_certificate.json',trans),('equation.json',final),('expanded_polynomial.json',poly),('METRICS.json',met)]:put(out,n,o)
    print(json.dumps(met,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('parent',type=Path)
    p.add_argument('out',type=Path)
    p.add_argument('--cap',type=int,default=16)
    p.add_argument('--merge',choices=['none','products','aggregate'],default='none')
    a=p.parse_args()
    build(a.parent,a.out,a.cap,a.merge)
