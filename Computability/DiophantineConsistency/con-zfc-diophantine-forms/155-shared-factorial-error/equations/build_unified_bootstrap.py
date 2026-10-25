#!/usr/bin/env python3
"""Emit the unified bootstrap budget with its full finite transformation.
Finite transformations are exact; the semantic proof is a separate argument.
"""
from pathlib import Path
import argparse,copy,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'parent252/code'))
import terminal_elimination as E
import translate_coordinates as T
def add(*ps):
    d={}
    for p in ps:
        for m,c in p.items():d[m]=d.get(m,0)+c
    return {m:c for m,c in d.items() if c}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--original-center',action='store_true');ap.add_argument('--affine-radix',action='store_true');args=ap.parse_args()
    old=json.loads((ROOT/'equation249/source.json').read_text());s=copy.deepcopy(old)
    n={v['name']:i for i,v in enumerate(s['variables'])};F=n['fact0.output'];B=n['choose0.output'];V=n['pow0.output'];M=n['pow14.output'];r=n['fact0.remainder'];slack=n['fact0.slack'];fb=n['mul.5']
    v=len(s['variables']);S=v+1
    s['variables'] += [{'name':'bootstrap.normalizing_ratio','kind':'signed_witness'},{'name':'bootstrap.normalized_ceiling_error','kind':'signed_witness'}]
    oldguard=next(r for r in s['residuals'] if r['label']=='domain_guard.4')
    expected_fb=E.normalize([[-1,[F,B]],[1,[fb]]]);changes=[];rows=[]
    for j,row in enumerate(s['residuals']):
        if row['label'] in ['fact0.ceiling','fact0.remainder_bound','domain_guard.0','domain_guard.1'] or E.normalize(row['terms'])==expected_fb:
            changes.append({'row':j,'before':row,'after':None});continue
        if row['label']=='domain_guard.4':
            new=dict(row,terms=E.as_terms(add(E.normalize(row['terms']),{(S,S):-4})))
            changes.append({'row':j,'before':row,'after':new});rows.append(new)
        elif row['label']=='cofinal.beta_base' and not args.affine_radix:
            new=dict(row,terms=E.as_terms(add(E.normalize(row['terms']),{(B,B):-1,(B,):2,():-1})))
            changes.append({'row':j,'before':row,'after':new});rows.append(new)
        elif row['label']=='radix.odd_square' and args.affine_radix:
            z=n['radix.odd_square_root_half']
            new={'label':'radix.odd_affine','terms':E.as_terms({(n['pow2.output'],):1,(z,):-2,():-1})}
            changes.append({'row':j,'before':row,'after':new});rows.append(new)
        else:rows.append(row)
    need_removed={r,slack,fb}
    if any(k in mm for row in rows for cc,mm in row['terms'] for k in need_removed):raise ValueError('Old factorial coordinate nonprivate')
    if len(changes)!=7:raise ValueError('Unexpected unified source delta')
    appended=[
      {'label':'bootstrap.normalization_ratio','terms':E.as_terms({(M,):1,tuple(sorted((B,v))):-1})},
      {'label':'bootstrap.normalized_ceiling','terms':E.as_terms({tuple(sorted((M,F))):1,tuple(sorted((v,V))):-1,(S,):-1})}
    ]
    rows+=appended
    if args.original_center:
        parent=json.loads((ROOT/'parent252/data/factored_source.json').read_text());replacement={r['label']:r for r in parent['residuals'] if r['label'] in ['cap.comparison_constructor','cap.index_residue']}
        rows=[replacement['cap.comparison_constructor'] if r['label']=='cap.deterministic_factor' else replacement.get(r['label'],r) for r in rows]
    s['residuals']=rows;s['variant']+=':unified_bootstrap_budget'+(':affine_odd_radix_old_beta' if args.affine_radix else '')
    p,pc,_=E.optimize(s,max_support=16);checked=E.verify(s,p,pc)
    oldp=json.loads((ROOT/'parent252/data/projected.json').read_text());oldt=json.loads((ROOT/'parent252/equation/translation_certificate.json').read_text());byname={oldp['variables'][i]['name']:d for i,d in oldt['shifts']}
    shifts={i:byname[x['name']] for i,x in enumerate(p['variables']) if x['name'] in byname}
    final=T.translate(p,shifts);poly=E.expand(final)
    m={'variables':len(final['variables']),'rows':len(final['residuals']),'degree':max(len(mm) for cc,mm in poly['terms']),'monomials':len(poly['terms']),'height':max(abs(cc) for cc,mm in poly['terms']),'row_height':max(abs(cc) for row in final['residuals'] for cc,mm in row['terms'])}
    out=ROOT/(('candidate245_original_center' if args.original_center else 'candidate244') if args.affine_radix else ('candidate246' if args.original_center else 'candidate245'));out.mkdir(exist_ok=True)
    data={'source.json':s,'source_delta.json':{'changes':changes,'appended':appended,'old_indices':{'F':F,'B':B,'V':V,'M':M,'r':r,'s':slack,'FBwire':fb},'new_indices':{'vB':v,'S':S},'original_center':args.original_center,'affine_radix':args.affine_radix,'beta_changed':not args.affine_radix,'semantic_status':'See the main report; this certificate verifies only the literal finite transformation.'},'projected.json':p,'projection_certificate.json':pc,'PROJECTION_CHECK.json':checked,'translation_certificate.json':{'shifts':[[i,d] for i,d in shifts.items()],'convention':'old=new+shift'},'equation.json':final,'expanded_polynomial.json':poly,'METRICS.json':m}
    for fn,obj in data.items():(out/fn).write_bytes(E.canonical_bytes(obj))
    print(json.dumps(m,sort_keys=True))
if __name__=='__main__':main()
