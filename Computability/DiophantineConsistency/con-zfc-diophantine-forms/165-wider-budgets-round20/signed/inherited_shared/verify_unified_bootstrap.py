#!/usr/bin/env python3
"""Independent exact verification of the245/246 integer bootstrap equations.

Does not import either producer.  The complete source mutation, projection,
translations, expansion, live-coordinate census and corruption controls are
verified. The semantic equivalence is proved in the research report.
"""
import argparse,copy,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'parent252/code'))
import terminal_elimination as E
from verify249 import read,need,sparse,terms,plus,multiply,translated

def expected_source(original_center,affine_radix=False):
    parent=read(ROOT.parent/'parent252/data/factored_source.json')
    md=read(ROOT.parent/'parent252/upstream/parent/transform_certificate.json')
    n={v['name']:i for i,v in enumerate(parent['variables'])}
    A,H,f,R,h=[n[k] for k in ['shared.A','cap.H','cap.f','cap.R','cap.h']]
    C=md['cap_variables']['Y'];F=n['fact0.output'];B=n['choose0.output'];V=n['pow0.output'];M=n['pow14.output'];q=n['pow2.output'];fb=n['mul.5']
    z=len(parent['variables']);v=z+1;S=z+2
    changes={}
    if not original_center:
        changes['cap.comparison_constructor']=dict(label='cap.deterministic_factor',terms=terms({(f,):1,(H,):-1,tuple(sorted((A,H))):1}))
        anchor=sparse(md['anchor_index'])
        changes['cap.index_residue']=dict(label='cap.index_residue',terms=terms(plus({(R,):1,tuple(sorted((C,h))):-1},{m:-c for m,c in anchor.items()})))
    removed_labels={'choose0.digit_bound','domain_guard.2','fact0.ceiling','fact0.remainder_bound','domain_guard.0','domain_guard.1'}
    expected=[];removed=[];changed=[]
    for i,r in enumerate(parent['residuals']):
        p=sparse(r['terms'])
        if r['label'] in removed_labels or p=={tuple(sorted((F,B))):-1,(fb,):1}:
            removed.append(i);continue
        if r['label']=='cofinal.beta_base' and not affine_radix:
            need(p=={(n['y'],):1,(V,):1,(V,V):-1},'Parent beta base differs')
            r=dict(r,terms=terms(plus(p,{(B,B):-1,(B,):2,():-1})));changed.append(i)
        elif r['label']=='domain_guard.4':
            r=dict(r,terms=terms(plus(p,{(S,S):-4})));changed.append(i)
        elif r['label'] in changes:r=changes[r['label']];changed.append(i)
        expected.append(r)
    need(len(removed)==7,'Wrong parent deletion count')
    radix_row=({'label':'radix.odd_affine','terms':terms({(q,):1,(z,):-2,():-1})} if affine_radix else {'label':'radix.odd_square','terms':terms({(q,):1,(z,z):-4,(z,):-4,():-1})})
    expected += [
      radix_row,
      {'label':'bootstrap.normalization_ratio','terms':terms({(M,):1,tuple(sorted((B,v))):-1})},
      {'label':'bootstrap.normalized_ceiling','terms':terms({tuple(sorted((M,F))):1,tuple(sorted((v,V))):-1,(S,):-1})}
    ]
    variables=parent['variables']+[
      {'name':'radix.odd_square_root_half','kind':'signed_witness'},
      {'name':'bootstrap.normalizing_ratio','kind':'signed_witness'},
      {'name':'bootstrap.normalized_ceiling_error','kind':'signed_witness'}]
    for r in expected:
        need(not any(k in mm for c,mm in r['terms'] for k in [n['fact0.remainder'],n['fact0.slack'],fb]),'Deleted old front wire is not private')
    oldpool=next(r for r in parent['residuals'] if r['label']=='cap.pooled_index_residue')
    need(next(r for r in expected if r['label']=='cap.pooled_index_residue')==oldpool,'Expected full orientation changed')
    return expected,variables,removed,changed

def audit(objs,original_center,affine_radix=False):
    source,projected,pc,eq,poly,meta,tr=objs
    expected,variables,removed,changed=expected_source(original_center,affine_radix)
    need(source['residuals']==expected,'Literal source residual delta mismatch')
    need(source['variables']==variables,'Literal source coordinate list mismatch')
    projection=E.verify(source,projected,pc)
    oldp=read(ROOT.parent/'parent252/data/projected.json');oldt=read(ROOT.parent/'parent252/equation/translation_certificate.json')
    byname={oldp['variables'][i]['name']:d for i,d in oldt['shifts']}
    shifts={i:byname[v['name']] for i,v in enumerate(projected['variables']) if v['name'] in byname}
    need(dict(tr['shifts'])==shifts and tr['convention']=='old=new+shift','Translation certificate differs')
    need(eq['variables']==projected['variables'],'Final coordinates differ')
    need(len(eq['residuals'])==len(projected['residuals']),'Final row count differs')
    acc={}
    for a,b in zip(projected['residuals'],eq['residuals']):
        p=translated(sparse(a['terms']),shifts)
        need(b['label']==a['label'] and sparse(b['terms'])==p,'Final polynomial translation differs')
        need(max(map(len,p),default=0)<=2,'Nonquadratic row')
        acc=plus(acc,multiply(p,p))
    need(sparse(poly['terms'])==acc,'Complete SOS expansion differs')
    need({v for m in acc for v in m}==set(range(len(eq['variables']))),'Inactive final coordinate')
    actual={'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max(map(len,acc)),'monomials':len(acc),'height':max(map(abs,acc.values())),'row_height':max(abs(c) for r in eq['residuals'] for c,m in r['terms'])}
    need(meta==actual,'Measured profile mismatch')
    if not affine_radix:
        target={'variables':246 if original_center else 245,'rows':182,'degree':4,'monomials':5306 if original_center else 5303,'height':128446,'row_height':256}
        need(actual==target,'Unexpected square-radix profile')
    else:need(actual['variables']==(245 if original_center else 244) and actual['rows']==181 and actual['degree']==4,'Unexpected affine-radix dimensions')
    return {'metrics':actual,'projection':projection,'deleted_parent_rows':removed,'changed_parent_rows':changed}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--original-center',action='store_true');ap.add_argument('--affine-radix',action='store_true');args=ap.parse_args()
    b=ROOT/(('candidate245_original_center' if args.original_center else 'candidate244') if args.affine_radix else ('candidate246' if args.original_center else 'candidate245'))
    files=['source.json','projected.json','projection_certificate.json','equation.json','expanded_polynomial.json','METRICS.json','translation_certificate.json']
    objs=[read(b/n) for n in files];result=audit(objs,args.original_center,args.affine_radix)
    controls=[]
    for label in ['bootstrap.normalization_ratio','bootstrap.normalized_ceiling','cofinal.beta_base','domain_guard.4','radix.odd_affine' if args.affine_radix else 'radix.odd_square','cap.pooled_index_residue']:
        xx=copy.deepcopy(objs);r=next(r for r in xx[0]['residuals'] if r['label']==label);r['terms'][0][0]+=1;controls.append((label,xx))
    xx=copy.deepcopy(objs);xx[3]['residuals'][0]['terms'][0][0]+=1;controls.append(('final translated coefficient',xx))
    xx=copy.deepcopy(objs);xx[4]['terms'][10][0]+=1;controls.append(('collected quartic coefficient',xx))
    xx=copy.deepcopy(objs);xx[6]['shifts'][0][1]+=1;controls.append(('translation shift',xx))
    rejected=[]
    for name,xx in controls:
        try:audit(xx,args.original_center,args.affine_radix)
        except ValueError:rejected.append(name)
        else:raise ValueError('Accepted corrupted artifact: '+name)
    result.update({'status':'PASS','optimized':bool(sys.flags.optimize),'rejected_controls':rejected,'scope':'Finite literal source mutation, inverse projection, coordinate translation and full coefficient identity. Unbounded semantic proof is separate.'})
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
