#!/usr/bin/env python3
"""Corrupt one literal/certificate at a time; every mutant must be rejected."""
from pathlib import Path
import tempfile, shutil, json,sys
P=Path(__file__).resolve().parent
sys.path.insert(0,str(P))
import check_signed_cap as C
results=[]
cases=['cap.norm','cap.auxiliary_divisibility','cap.squared_aggregate','cap.pooled_index_residue','cap.comparison_ordinate','retained_semantic_row','expanded_coefficient','extra_cap_row','duplicate_cap_row','cap_certificate_hash','factor_certificate','projection_certificate','parent_input']
for endpoint in ['signed_cap','odd_cap']:
 original=P/endpoint
 for target in cases:
  with tempfile.TemporaryDirectory() as td:
   dest=Path(td)/'mutation';shutil.copytree(original,dest)
   file=dest/'raw_equation.json'
   if target=='expanded_coefficient':file=dest/'expanded_polynomial.json'
   if target=='cap_certificate_hash':file=dest/'cap_certificate.json'
   if target=='factor_certificate':file=dest/'factorization_certificate.json'
   if target=='projection_certificate':file=dest/'projection_certificate.json'
   if target=='parent_input':
    parentcopy=Path(td)/'source';parentcopy.mkdir();shutil.copy(P/'source/parent_source.json',parentcopy/'parent_source.json');file=parentcopy/'parent_source.json';C.P=Path(td)
   v=json.loads(file.read_text())
   if target=='expanded_coefficient':v['terms'][0][0]+=1
   elif target=='cap_certificate_hash':v['parent_sha256']='0'*64
   elif target=='factor_certificate':v['changes'][0]['new'][0][0]+=1
   elif target=='projection_certificate':v['steps'][0]['restoration'][0][0]+=1
   elif target=='extra_cap_row':v['residuals'].append({'label':'cap.unverified','terms':[[1,[]]]})
   elif target=='duplicate_cap_row':v['residuals'].append(next(r for r in v['residuals'] if r['label']=='cap.norm'))
   else:
    row=v['residuals'][0] if target in ['retained_semantic_row','parent_input'] else next(r for r in v['residuals'] if r['label']==target)
    row['terms'][0][0]+=1
   file.write_text(json.dumps(v))
   try:C.check(dest)
   except (ValueError,KeyError) as e:results.append({'endpoint':endpoint,'mutation':target,'status':'REJECTED','reason':str(e)})
   else:raise ValueError('mutation accepted '+target)
   finally:C.P=P
(P/'MUTATION_CHECKS.json').write_text(json.dumps({'status':'PASS','tests':results},indent=2)+'\n')
print(json.dumps({'status':'PASS','rejected':len(results)},indent=2))
