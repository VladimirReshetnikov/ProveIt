#!/usr/bin/env python3
"""Compress five square-frame atoms and adopt the two-square center theorem."""
from pathlib import Path
import argparse,copy,hashlib,json,sys
HERE=Path(__file__).resolve().parent
PACKAGED=(HERE.parent/'stages').is_dir()
PARENT=(HERE.parent/'upstream/factorial_free/direct' if PACKAGED else HERE.parents[1]/'sources/incoming/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/direct')
SOURCE=HERE.parent/'stages/modular' if PACKAGED else HERE.parent/'literature_audit/modular'
OUT=HERE.parent/'stages/compressed' if PACKAGED else HERE/'frame_compressed'

def build(source=SOURCE,out=OUT,parent=PARENT):
    sys.path.insert(0,str(parent/'parent/code'))
    import terminal_elimination as E
    import factor_horn as F
    import translate_coordinates as T
    old=json.loads((source/'raw_source.json').read_text());new=copy.deepcopy(old)
    names={v['name']:i for i,v in enumerate(old['variables'])}
    t=F.add(F.V(names['t0']),{():16});q=F.V(names['pow2.output']);R=F.V(names['radius.R'])
    removed=[{():16},F.add(t,{():1}),F.add(q,{():1}),R,F.V(names['pow6.output'])]
    idx=next(i for i,r in enumerate(old['residuals']) if r['label']=='shared.frame_definition')
    before=E.normalize(old['residuals'][idx]['terms'])
    after=F.add(before,*[E.multiply(a,a) for a in removed])
    new['residuals'][idx]['terms']=E.as_terms(after)
    ci=next(i for i,r in enumerate(old['residuals']) if r['label']=='free_A.cofinal_constructor')
    w=names['free_A.w']
    new['residuals'][ci]['terms']=E.as_terms(F.add(E.normalize(old['residuals'][ci]['terms']),{(w,w):1,(w,):1}))
    new['variant']='common_modular_numerators_affine_frame_two_square_center'
    mutation={'schema':'frame_affine_bounds_v1','source_sha256':hashlib.sha256((source/'raw_source.json').read_bytes()).hexdigest(),
        'row':idx,'old_row':old['residuals'][idx],'new_row':new['residuals'][idx],
        'removed_square_atoms':[E.as_terms(a) for a in removed],
        'bound':'W>=t^2+2>=258; |16|,|t+1|,|q+1|<W; R^2<=2((R+t)^2+t^2)<=2(W-2)<W^2',
        'successor_output_reason':'pow6.output=q*pow4.output is a derived exact product, not a bounded power request',
        'center_change':{'row':ci,'removed_variable':w,'old_row':old['residuals'][ci],'new_row':new['residuals'][ci],
            'theorem':'Two-square cofinal completion with odd-multiple frame index, all primes of NM dividing q'}}
    fac,fc=F.transform(new);pr,pc,met=E.optimize(fac,max_support=16);check=E.verify(fac,pr,pc)
    op=json.loads((parent/'parent/data/projected.json').read_text());ot=json.loads((parent/'parent/equation/translation_certificate.json').read_text())
    byname={op['variables'][i]['name']:s for i,s in ot['shifts']}
    shifts={i:byname[v['name']] for i,v in enumerate(pr['variables']) if v['name'] in byname}
    eq=T.translate(pr,shifts);poly=E.expand(eq)
    metrics={'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max(len(m) for _,m in poly['terms']),
        'monomials':len(poly['terms']),'height':max(abs(c) for c,_ in poly['terms']),'row_height':max(abs(c) for r in eq['residuals'] for c,_ in r['terms'])}
    out.mkdir(parents=True,exist_ok=True)
    values=[('raw_source.json',new),('mutation.json',mutation),('factored_source.json',fac),('factorization_certificate.json',fc),
        ('projected.json',pr),('projection_certificate.json',pc),('projection_check.json',check),
        ('translation_certificate.json',{'convention':'old=new+shift','shifts':sorted(shifts.items())}),
        ('equation.json',eq),('expanded_polynomial.json',poly),('METRICS.json',metrics)]
    for name,obj in values:(out/name).write_bytes(E.canonical_bytes(obj))
    print(json.dumps(metrics,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--parent',type=Path,default=PARENT)
    ap.add_argument('--source',type=Path,default=SOURCE)
    ap.add_argument('--output',type=Path,default=OUT)
    a=ap.parse_args();build(a.source,a.output,a.parent)
