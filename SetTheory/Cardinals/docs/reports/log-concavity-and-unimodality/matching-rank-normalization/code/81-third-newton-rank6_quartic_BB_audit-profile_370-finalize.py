#!/usr/bin/env python3
"""Validate and summarize the dual exact BB (3,7,0) certificate."""
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
PEER=HERE.parent/'profile_370_independent'
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def require(test,message):
    if not test:raise ArithmeticError(message)

mapping=[('zero_overlap_zero','zero0'),('zero','zero'),('zero_overlap_h','h0'),('g','g'),('h','h')]
rows=[]
for primary,peer in mapping:
    f=HERE/('certificate_'+primary+'.json')
    g=PEER/('check_'+peer+'.json')
    a=json.loads(f.read_text());b=json.loads(g.read_text())
    require(a['status']=='pass' and b['all_pass'],'nonpassing region')
    require(a['scalar_sha256']==b['scalar_sha256']==digest(HERE/'schur.txt'),'scalar hash')
    require(a['coefficient_sha256']==b['coefficient_sha256'],'coefficient hash mismatch')
    require(a['positive_coefficients']==b['positive_coefficients'],'positive coefficient count')
    source='check_zero_overlap.py' if primary.startswith('zero_overlap') else 'check_regions.py'
    require(a['verifier_sha256']==digest(HERE/source),'primary verifier changed')
    rows.append({'region':primary,'positive_coefficients':a['positive_coefficients'],
                 'coefficients_including_zeros':a['coefficients_including_zeros'],
                 'coefficient_sha256':a['coefficient_sha256'],
                 'primary_record':f.name,'independent_record':str(g.relative_to(HERE.parent))})
scalar=json.loads((HERE/'scalar_certificate.json').read_text())
support=json.loads((HERE/'support_count_certificate.json').read_text())
independent_scalar=json.loads((PEER/'check_scalar.json').read_text())
require(scalar['status']==support['status']=='pass' and independent_scalar['all_pass'],'matrix/support gate')
require(scalar['cross_sha256']==digest(HERE/'cross.json'),'cross source changed')
require(scalar['verifier_sha256']==digest(HERE/'derive_scalar.py'),'scalar verifier changed')
require(support['verifier_sha256']==digest(HERE/'check_support_counts.py'),'support verifier changed')
files=('proof.md','README.md','schur.txt','cross.json','derive_scalar.py','check_support_counts.py',
       'check_zero_overlap.py','check_regions.py','scalar_certificate.json','support_count_certificate.json',
       'certificate_zero_overlap_zero.json','certificate_zero.json','certificate_zero_overlap_h.json',
       'certificate_g.json','certificate_h.json','finalize.py')
record={'status':'complete','profile':[3,7,0],'scope':'Unit left activities, arbitrary integer L populations; BB class matrix and finite labeled R Hessians',
        'all_five_dual_hashes_match':True,'independent_full_matrix_identities':independent_scalar['quadratic_coefficient_identities'],
        'exact_endpoint_polynomial_identities':support['exact_polynomial_identities'],
        'positive_coefficients':sum(r['positive_coefficients'] for r in rows),
        'coefficients_including_zeros':sum(r['coefficients_including_zeros'] for r in rows),
        'negative_coefficients':0,'regions':rows,'sha256':{f:digest(HERE/f) for f in files}}
(HERE/'manifest.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ('status','all_five_dual_hashes_match','positive_coefficients','coefficients_including_zeros','negative_coefficients')},indent=2))
