#!/usr/bin/env python3
"""Four symmetric remainder budgets for the literal signed C222 source.

New code prepared with AI assistance, 25 October 2026.
The source, factorization and monic projection dependencies are retained.
"""
from pathlib import Path
import argparse, copy, hashlib, json, sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'vendor'))
import terminal_elimination as E
import factor_horn as F
import translate_coordinates as T

def put(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(E.canonical_bytes(data))

def sha(data):
    return hashlib.sha256(E.canonical_bytes(data)).hexdigest()

def make_source(merge=False, odd_radix=False):
    parent = json.loads((HERE/'inherited/guarded.json').read_text())
    cert = json.loads((HERE/'inherited/source_certificate.json').read_text())
    e = copy.deepcopy(parent)
    e.pop('metrics', None)
    e['variant'] += ':symmetric_digit_pools' + (':merged_t' if merge else '') + (':odd_square_radix' if odd_radix else '')
    names = {v['name']: i for i, v in enumerate(e['variables'])}
    group_specs = [
        ('t', 'pow4.output', ['choose0.remainder','range8.remainder']),
        ('tplus1','pow6.output',[f'range{i}.remainder' for i in [0,1,2,3,9]]),
        ('yplus1','pow11.output',[f'range{i}.remainder' for i in [4,5]]),
        ('x','pow14.output',[f'range{i}.remainder' for i in [6,7]]),
    ]
    obsolete = []
    removed_aux = []
    for j, g in enumerate(cert['guards']):
        if g['kind']=='postsemantic_interval' or (odd_radix and g['kind']=='front_nonnegative' and g['coordinate']==names['choose0.oslack']):
            obsolete.append('domain_guard.'+str(j))
            removed_aux.extend(g['auxiliary'])
    if len(obsolete)!=11+int(odd_radix):
        raise ValueError('Incorrect old guard deletion census')
    removed = [r for r in e['residuals'] if r['label'] in obsolete]
    if len(removed)!=11+int(odd_radix):
        raise ValueError('Incorrect guard source binding')
    e['residuals'] = [r for r in e['residuals'] if r['label'] not in obsolete]
    radix_square = None
    if odd_radix:
        z=len(e['variables']);q=names['pow2.output']
        e['variables'].append({'name':'odd_radix.root','kind':'signed_witness'})
        radix_square={'root':z,'radix':q,'row':len(e['residuals'])}
        e['residuals'].append({'label':'odd_radix.square','terms':E.as_terms({(q,):1,(z,z):-4,(z,):-4,():-1})})
    groups = []
    for tag, denominator, remainders in group_specs:
        groups.append({'tag':tag,'denominator':names[denominator],
                       'remainders':[names[n] for n in remainders]})
    scaled = []
    if merge:
        q = names['pow2.output']
        for r in groups[0]['remainders']:
            z = len(e['variables'])
            e['variables'].append({'name':'digit_pool.scaled.'+e['variables'][r]['name'], 'kind':'gate'})
            e['residuals'].append({'label':'digit_pool.scale.'+e['variables'][r]['name'],
                                  'terms':E.as_terms(F.add(F.V(z),F.neg(E.multiply(F.V(q),F.V(r)))))})
            scaled.append({'input':r,'output':z,'factor':q})
        groups[1]['remainders'] += [s['output'] for s in scaled]
        groups[1]['tag']='t_and_tplus1'
        groups=groups[1:]
    for group in groups:
        D=group['denominator']
        aux=list(range(len(e['variables']),len(e['variables'])+3))
        e['variables'] += [{'name':f"digit_pool.{group['tag']}.{s}",'kind':'integer_guard'} for s in ('a','b','c')]
        p={(D,D):1,():-1}
        for r in group['remainders']:
            p[(r,r)]=p.get((r,r),0)-4
        a,b,c=aux
        for m,v in [((a,a),-1),((b,b),-1),((c,c),-1),((c,),-1)]:
            p[m]=p.get(m,0)+v
        group.update(auxiliary=aux,row=len(e['residuals']))
        e['residuals'].append({'label':'digit_pool.'+group['tag'],'terms':E.as_terms(p)})
    delta={'schema':'symmetric_digit_pool_v1','parent_sha256':sha(parent),'target_sha256':sha(e),
           'removed_guard_rows':removed,'removed_private_auxiliaries':removed_aux,
           'groups':groups,'scaled_remainders':scaled,'odd_radix':radix_square,
           'source_certificate_sha256':sha(cert)}
    return e,delta

def build(out, merge=False, support=16, odd_radix=False):
    source, delta=make_source(merge,odd_radix)
    factored, fc=F.transform(source)
    projected, pc, metrics=E.optimize(factored,max_support=support)
    receipt=E.verify(factored,projected,pc)
    shifts={i:-1 for i,v in enumerate(projected['variables']) if v['name'].startswith('crt.encoded') or v['name'].endswith('minus1')}
    for i,v in enumerate(projected['variables']):
        if v['name']=='t0':shifts[i]=-16
    final=T.translate(projected,shifts)
    polynomial=E.expand(final)
    tr={'schema':'integral_translation_v1','input_sha256':sha(projected),'output_sha256':sha(final),
        'shifts':[[i,d] for i,d in sorted(shifts.items())],'convention':'old=new+shift'}
    exact={'variables':len(final['variables']),'rows':len(final['residuals']),
           'degree':max(len(m) for c,m in polynomial['terms']),
           'monomials':len(polynomial['terms']),
           'height':max(abs(c) for c,m in polynomial['terms']),
           'row_height':max(abs(c) for r in final['residuals'] for c,m in r['terms']),
           'groups':len(delta['groups']),'merged':merge,'projection_support':support,'odd_radix':odd_radix}
    for name,obj in [('source.json',source),('delta_certificate.json',delta),('factored_source.json',factored),
                     ('factorization_certificate.json',fc),('projected.json',projected),
                     ('projection_certificate.json',pc),('translation_certificate.json',tr),
                     ('equation.json',final),('expanded_polynomial.json',polynomial),
                     ('METRICS.json',exact),('PROJECTION_CHECK.json',receipt)]:
        put(out/name,obj)
    print(json.dumps(exact,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('out',type=Path)
    ap.add_argument('--merge',action='store_true')
    ap.add_argument('--support',type=int,default=16)
    ap.add_argument('--odd-radix',action='store_true')
    args=ap.parse_args()
    build(args.out,args.merge,args.support,args.odd_radix)
