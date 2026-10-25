#!/usr/bin/env python3
"""Fused signed-bootstrap certificate on the frozen common-remainder source.
All edits stay in scratch. Correctness proof is BOOTSTRAP_PROOF.md.
"""
from pathlib import Path
import sys,json,copy,hashlib,argparse
ROOT=Path(__file__).resolve().parent
BASE=ROOT/'upstream_common'
sys.path.insert(0,str(BASE/'code'))
import terminal_elimination as E
import factor_horn as F
import translate_coordinates as T

def sha(o):return hashlib.sha256(E.canonical_bytes(o)).hexdigest()
def write(p,o):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(E.canonical_bytes(o))
def build(out,cap=16):
 source=json.loads((BASE/'data/source.json').read_text())
 old=copy.deepcopy(source)
 oldguards=json.loads((BASE/'data/remainder_transformation.json').read_text())['new_guards']
 names={v['name']:i for i,v in enumerate(source['variables'])};i=names.__getitem__
 r,s,q,o=i('fact0.remainder'),i('fact0.slack'),i('pow2.output'),i('choose0.oslack')
 for k in (r,s,o):
  matched=[g for g in oldguards if g.get('coordinate')==k]
  if len(matched)!=1 or matched[0]['kind']!='front_nonnegative':raise ValueError('guard mismatch')
 source['residuals']=[row for row in source['residuals'] if row['label']!='choose0.digit_bound']
 z=len(source['variables']);source['variables'].append({'name':'bootstrap.odd_square_root','kind':'signed_witness'})
 source['residuals'].append({'label':'bootstrap.odd_square_radix','terms':E.as_terms({(q,):1,(z,z):-4,(z,):-4,():-1})})
 guards=[{'kind':'fused_factorial_signs','expression':E.as_terms({(r,s):1,(r,):1,(s,):1})}]+[{k:v for k,v in g.items() if k not in ('row','auxiliary')} for g in oldguards if g['kind']!='front_nonnegative']
 guardrecords=[]
 for no,g in enumerate(guards):
  aux=list(range(len(source['variables']),len(source['variables'])+3));a,b,c=aux
  source['variables'] += [{'name':f'bootstrap.guard{no}.{x}','kind':'integer_guard'} for x in ('a','b','c')]
  pol=E.normalize(g['expression']);pol=F.add(pol,{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})
  rec={**g,'auxiliary':aux,'row':len(source['residuals'])};guardrecords.append(rec)
  source['residuals'].append({'label':f'bootstrap.guard{no}','terms':E.as_terms(pol)})
 source['variant']+=':fused_factorial_signs_and_odd_square'
 factored,fc=F.transform(source)
 out=Path(out);write(out/'source/source.json',source);write(out/'source/factored.json',factored);write(out/'source/factorization_certificate.json',fc)
 transf={'schema':'fused_sign_bootstrap_v1','parent_source_sha256':sha(old),'source_sha256':sha(source),'original_guard_coordinates':[r,s,o],'fused_front_coordinates':[r,s],'radix_coordinate':q,'odd_square_root_coordinate':z,'guard_records':guardrecords,'removed_row_labels':['choose0.digit_bound'],'proof':'BOOTSTRAP_PROOF.md'}
 write(out/'source/transformation.json',transf)
 oldprojected=json.loads((BASE/'data/projected.json').read_text());oldtr=json.loads((BASE/'equation/translation_certificate.json').read_text())
 shiftmap={oldprojected['variables'][j]['name']:s for j,s in oldtr['shifts']}
 profiles=[('integer248',16,False),('integer246',12,True),('integer245',24,True)]
 allmetrics={}
 for profile,cap,quadraticfirst in profiles:
  projected,pc,metric=E.optimize(factored,max_support=cap,quadratic_first=quadraticfirst)
  E.verify(factored,projected,pc)
  shifts={j:shiftmap[v['name']] for j,v in enumerate(projected['variables']) if v['name'] in shiftmap}
  final=T.translate(projected,shifts);poly=E.expand(final)
  metrics={'variables':len(final['variables']),'residuals':len(final['residuals']),'degree':max(len(m) for c,m in poly['terms']),'monomials':len(poly['terms']),'height':max(abs(c) for c,m in poly['terms'])}
  trans={'schema':'integral_translation_v1','convention':'old=new+shift','input_sha256':sha(projected),'output_sha256':sha(final),'shifts':[[j,s] for j,s in shifts.items()],'reused_source':'Common_Remainders/direct/equation/translation_certificate.json by matched variable name'}
  for n,obj in [('projected.json',projected),('projection_certificate.json',pc),('translation_certificate.json',trans),('equation.json',final),('expanded_polynomial.json',poly),('METRICS.json',metrics)]:write(out/'equations'/profile/n,obj)
  allmetrics[profile]=metrics
 return allmetrics
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();print(json.dumps(build(a.output),indent=2))
