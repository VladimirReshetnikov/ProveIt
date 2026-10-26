#!/usr/bin/env python3
"""Replay attributed affine exposures on the new source."""
from pathlib import Path
import copy,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'baseline/direct'))
import build_affine as A
import translate_coordinates as T
E,F=A.E,A.F

def main():
    old=json.loads((ROOT/'diagonal_raw/equation.json').read_text())
    names={v['name']:i for i,v in enumerate(old['variables'])}
    for dense in [False,True]:
        n=len(old['variables'])-(4 if dense else 3)
        cert={'schema':'affine_exposure_v1','endpoint':'diagonal'+str(n),
          'coordinate_shears':copy.deepcopy(A.SHEARS),
          'row_operations':[[i-1,j-1,k] for i,j,k in A.ROWS],
          'projections':[],'final_row_operations':[],
          'attribution':'Six coordinate shears and the affine exposure pattern are inherited from Factorial-Free Binomial CRT; row indices shift by one after R=F.'}
        rows=[E.normalize(r['terms']) for r in old['residuals']]
        for target,inputs in cert['coordinate_shears']:
            t=names[target];rest=F.add(F.V(t),{(names[n],):c for n,c in inputs.items()})
            rows=[E.substitute(r,t,rest) for r in rows]
        for i,j,k in cert['row_operations']:rows[i]=F.add(rows[i],{m:k*c for m,c in rows[j].items()})
        proj=[(i-1,n) for i,n in A.PROJECT]+([(89,'add.380')] if dense else [])
        for i,name in proj:
            t=names[name];q=E.candidate(rows[i],t,False)
            if q is None or E.degree(q)>1:raise ValueError(('affine exposure failed',i,name))
            cert['projections'].append({'row':i,'variable':t,'name':name,'replacement':E.as_terms(q)})
            rows=[E.substitute(r,t,q) for r in rows]
        eq,poly,metric=A.construct(old,cert)
        out=ROOT/cert['endpoint']
        for f,obj in [('certificate.json',cert),('equation.json',eq),('expanded_polynomial.json',poly),('METRICS.json',metric)]:A.put(out/f,obj)
        print(cert['endpoint'],json.dumps(metric,sort_keys=True))
        parent_count=241 if dense else 242
        parent=json.loads((ROOT/'baseline/direct'/f'factorial_free_affine{parent_count}_balanced/certificate.json').read_text())
        balanced=copy.deepcopy(cert)
        balanced['endpoint'] += '_balanced'
        balanced['final_row_operations']=[[i-1,j-1,k] for i,j,k in parent['final_row_operations']]
        balanced['attribution'] += ' Final 34/36 row operations are transferred from the same parent with indices shifted by one.'
        eq,poly,metric=A.construct(old,balanced)
        out=ROOT/balanced['endpoint']
        for f,obj in [('certificate.json',balanced),('equation.json',eq),('expanded_polynomial.json',poly),('METRICS.json',metric)]:A.put(out/f,obj)
        print(balanced['endpoint'],json.dumps(metric,sort_keys=True))
        z=next(i for i,v in enumerate(eq['variables']) if v['name']=='radix.odd_multiple_of_three_parameter')
        centered=T.translate(eq,{z:-1})
        centered_name='diagonal'+str(n)+'_centered'
        for name,obj in [('translation_certificate.json',{'source':balanced['endpoint'],'convention':'old=new+shift','shifts':[[z,-1]]})]:A.put(ROOT/centered_name/name,obj)
        export(centered,ROOT/centered_name)
        frame=next(i for i,r in enumerate(centered['residuals']) if r['label']=='shared.frame_definition')
        candidates=[i for i,r in enumerate(centered['residuals']) if E.normalize(r['terms']).get((z,z))==36]
        if len(candidates)!=1:raise ValueError('unique quadratic radix row for final cancellation')
        j=candidates[0]
        reduced=copy.deepcopy(centered)
        pp=F.add(E.normalize(reduced['residuals'][frame]['terms']),{m:2*c for m,c in E.normalize(reduced['residuals'][j]['terms']).items()})
        reduced['residuals'][frame]['terms']=E.as_terms(pp)
        reduced_name='diagonal'+str(n)+'_reduced'
        A.put(ROOT/reduced_name/'row_certificate.json',{'source':centered_name,'operations':[[frame,j,2]]})
        export(reduced,ROOT/reduced_name)

def export(eq,out):
    ep=E.expand(eq)
    metric={'variables':len(eq['variables']),'rows':len(eq['residuals']),
      'degree':max(len(m) for _,m in ep['terms']),'monomials':len(ep['terms']),
      'height':max(abs(c) for c,_ in ep['terms']),
      'row_height':max(abs(c) for row in eq['residuals'] for c,_ in row['terms'])}
    for f,obj in [('equation.json',eq),('expanded_polynomial.json',ep),('METRICS.json',metric)]:A.put(out/f,obj)
    print(out.name,json.dumps(metric,sort_keys=True))

if __name__=='__main__':main()
