#!/usr/bin/env python3
"""Compile the even-frame, doubled-abscissa signed C222 quartic."""
from pathlib import Path
import argparse, copy, hashlib, json, sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'vendor'))
import terminal_elimination as E
import factor_horn as F
import translate_coordinates as T
from center_integer import center
add,neg,V=F.add,F.neg,F.V
mul=E.multiply

def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(E.canonical_bytes(value))

def sha(value):
    return hashlib.sha256(E.canonical_bytes(value)).hexdigest()

def build(output,cap=16,baseline=False,parity_only=False,orient=False,odd_radix=False,linear_cofinal=False):
    original=json.loads((ROOT/'input/source.json').read_text())
    oldcert=json.loads((ROOT/'input/transform_certificate.json').read_text())
    source=copy.deepcopy(original)
    names={v['name']:i for i,v in enumerate(source['variables'])}
    W,A=names['shared.W'],names['shared.A']
    cv=oldcert['cap_variables']; J,e,Y=cv['J'],cv['e'],cv['Y']
    Y2=oldcert['cap_square_variable']
    modifications=[]
    if odd_radix and not orient:raise ValueError('Odd radix requires oriented abscissas')
    if not baseline:
        for i,row in enumerate(source['residuals']):
            p=E.normalize(row['terms']);q=None
            if row['label']=='shared.frame_definition':
                # p=W-2-sum(atom^2); new W=2+2 sum(atom^2).
                q=add({m:2*c for m,c in p.items()},neg(V(W)),{():2})
            elif row['label']=='cap.common_multiple':
                q=add(V(J),{(Y2,e):-4,(Y2,):-2})
            elif orient and row['label']=='cap.pooled_index_residue':
                q=p.copy()
                for sd in oldcert['seed_data']:
                    x=sd['pair'][0]
                    q=add(q,{(x,x):1,(x,):-2,():1})
            elif orient and row['label']=='self_radix.base_definition':
                reps=[i for i,v in enumerate(source['variables']) if v['name'].startswith('crt.encoded')]
                factor=2 if odd_radix else 1
                constant=3 if odd_radix else 2
                hpoly=add({():constant+factor*len(reps)},*[{(i,):factor} for i in reps])
                q=add(V(names['self_radix.BH']),neg(mul(V(names['choose0.output']),hpoly)))
            elif linear_cofinal and row['label']=='cofinal.beta_base':
                q=add(V(names['y']),neg(V(names['pow0.output'])),{():1})
            if q is not None:
                new=dict(row,terms=E.as_terms(q))
                modifications.append({'row':i,'old':row,'new':new})
                source['residuals'][i]=new
        if not parity_only:
            a=len(source['variables'])
            source['variables'].append({'name':'even_frame.half_abscissa','kind':'signed_witness'})
            source['residuals'].append({'label':'even_frame.doubled_abscissa','terms':E.as_terms(add(V(A),{(a,a):-2,():1}))})
        if odd_radix:
            r=len(source['variables'])
            source['variables'].append({'name':'odd_radix.half_root','kind':'signed_witness'})
            source['residuals'].append({'label':'odd_radix.square','terms':E.as_terms(add(V(names['pow2.output']),{(r,r):-4,(r,):-4,():-1}))})
    guards=[]
    for g in oldcert['guards']:
        if not baseline and g['kind']=='anchor_common_multiplier':continue
        if not baseline and not parity_only and g.get('coordinate')==A:continue
        if orient and g.get('coordinate') is not None and source['variables'][g['coordinate']]['name'].startswith('crt.encoded'):continue
        if orient and g.get('coordinate')==names['x']:continue
        if odd_radix and g.get('coordinate')==names['choose0.oslack']:continue
        guards.append({k:v for k,v in copy.deepcopy(g).items() if k not in ('row','auxiliary')})
    guarded=copy.deepcopy(source)
    for j,g in enumerate(guards):
        a,b,c=range(len(guarded['variables']),len(guarded['variables'])+3)
        guarded['variables'] += [{'name':f'guard{j}.{s}','kind':'integer_guard'} for s in ('a','b','c')]
        row=add(E.normalize(g['expression']),{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})
        g.update({'row':len(guarded['residuals']),'auxiliary':[a,b,c]})
        guarded['residuals'].append({'label':f'domain_guard.{j}','terms':E.as_terms(row)})
    guarded['variant']+=':even_frame_odd_anchor'+(':doubled_abscissa' if not parity_only else '')
    factored,fc=F.transform(guarded)
    projected,pc,metrics=E.optimize(factored,max_support=cap)
    replay=E.verify(factored,projected,pc)
    shifts={i:-1 for i,v in enumerate(projected['variables']) if v['name'].startswith('crt.encoded') or v['name'].endswith('minus1')}
    for i,v in enumerate(projected['variables']):
        if v['name']=='t0':shifts[i]=-16
    final=T.translate(projected,shifts)
    poly=E.expand(final)
    metrics={'variables':len(final['variables']),'rows':len(final['residuals']),'degree':max(len(m) for c,m in poly['terms']),'monomials':len(poly['terms']),'height':max(abs(c) for c,m in poly['terms']),'row_height':max(abs(c) for r in final['residuals'] for c,m in r['terms']),'guards':len(guards),'support_cap':cap,'baseline':baseline,'parity_only':parity_only,'orient_all_abscissas':orient,'odd_radix':odd_radix,'linear_cofinal':linear_cofinal}
    trans={'schema':'integral_translation_v1','input_sha256':sha(projected),'output_sha256':sha(final),'shifts':[[i,s] for i,s in shifts.items()],'convention':'old=new+shift'}
    change={'schema':'even_frame_odd_anchor_v1','input_sha256':sha(original),'parent_transform_sha256':sha(oldcert),'modifications':modifications,'guards':guards,'new_source_sha256':sha(source),'domain':'unrestricted integers','options':{'baseline':baseline,'parity_only':parity_only,'orient':orient,'odd_radix':odd_radix,'linear_cofinal':linear_cofinal},'meaning':'W=2+2 sum atoms^2; A=2a^2-1 unless parity_only; J=2 C^2(2e+1); optional orientation and odd square radix.'}
    for n,o in [('source.json',source),('guarded.json',guarded),('transform_certificate.json',change),('factored_source.json',factored),('factorization_certificate.json',fc),('projected.json',projected),('projection_certificate.json',pc),('PROJECTION_CHECK.json',replay),('translation_certificate.json',trans),('equation.json',final),('expanded_polynomial.json',poly),('METRICS.json',metrics)]:write(output/n,o)
    print(json.dumps(metrics,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'generated');p.add_argument('--cap',type=int,default=16);p.add_argument('--baseline',action='store_true');p.add_argument('--parity-only',action='store_true');p.add_argument('--orient',action='store_true');p.add_argument('--odd-radix',action='store_true');p.add_argument('--linear-cofinal',action='store_true');p.add_argument('--center',action='store_true');args=p.parse_args()
    build(args.output,args.cap,args.baseline,args.parity_only,args.orient,args.odd_radix,args.linear_cofinal)
    if args.center:center(args.output,args.output/'centered')
