"""Verify the integrity and reported outcomes of the committed release evidence.

This reads pinned receipts; it does not rerun mathematics or perform visual QA.
"""
from pathlib import Path
from fractions import Fraction
from decimal import Decimal
import hashlib, json, sys
# The committed exact endpoints contain up to several thousand integer digits.
sys.set_int_max_str_digits(100000)
B=Path(__file__).resolve().parents[1]
V=B/'verification'
def read(name):return json.loads((V/name).read_text(encoding='utf-8'))
def digest(path,normalized):
    data=path.read_bytes()
    return hashlib.sha256(data.replace(b'\r\n',b'\n') if normalized else data).hexdigest()
changed=[name for name,h in read('source-sha256.json').items()
         if not (B/name).is_file() or digest(B/name,True)!=h]
dependencies=read('dependency-sha256.json')
changed_dependencies=[name for name,entry in dependencies.items()
    if not (B/name).is_file() or digest(B/name,entry['mode']=='lf-normalized')!=entry['sha256']]
pdfhash=digest(B/'polylogarithms.pdf',False)
build=read('build-results.json');render=read('pdf-inspection.json');doc=read('document-integrity.json')
outcomes={}
for name,count in [('wolfram-results.json',31),('mpmath-results.json',67),
                   ('additional-corrections-results.json',5),('nielsen-inversion-results.json',4)]:
    x=read(name);outcomes[name]=x['all_pass'] and len(x['checks'])==count
x=read('inverse-euler-results.json')
outcomes['inverse-euler-results.json']=x['status']=='all checks passed' and all(
 len(x[k])==n for k,n in [('exact_partial_fraction_checks',64),('mixed_reduction_checks',18),
 ('explicit_survivor_reductions',4),('euler_sum_checks',5),('generator_checks',6),('residue_checks',3)])
x=read('rank-bridge-results.json')
outcomes['rank-bridge-results.json']=x['passed'] and sum(x['rank_checks'].values())==594 and len(x['bridge_checks']['cases'])==12
x=read('harmonic-replay/verification_summary.json')
outcomes['harmonic-replay']=x['status']=='PASS' and x['consistency_checks']==156 and x['total_recorded_cases']==168
x=read('zero-sign-results.json')
outcomes['zero-sign-results.json']=x['status']=='PASS' and x['evaluations']==30 and all(r['expected_sign']==r['verified_sign'] for r in x['results'])
x=read('cubic-class-results.json');outcomes['cubic-class-results.json']=x['all_passed'] and len(x['fields'])==5
x=read('cyclotomic-results.json');outcomes['cyclotomic-results.json']=x['passed'] and len(x['checks'])==40 and x['zero_conductors']==[1,2,3,4,5,6,8,10,12,24]
x=read('J-evaluation-results.json');outcomes['J-evaluation-results.json']=x['case_count']==25 and all(c['passed'] for c in x['cases'])
x=read('modular-row-results.json');outcomes['modular-row-results.json']=x['summary']['all_checks_passed'] and all(c['passed'] for k in ['single_row_identity_checks','CM_checks','tail_checks'] for c in x[k])
x=read('spectral-replay/data/parameter_asymptotics.json');outcomes['spectral-replay']=x['status']=='passed' and x['rational_certificates']['certificate_count']==44 and x['rational_certificates']['independent_exact_coefficient_comparisons']==40 and x['rational_certificates']['positive_sign_certificates']==40 and x['spectral_tail_checks']['count']==16
def rational(endpoint):return Fraction(int(endpoint['numerator']),int(endpoint['denominator']))
x=read('Herglotz-interval-results.json')
outcomes['Herglotz-interval-results.json']=len(x['cases'])==4 and all(rational(c['F_interval']['lower'])<rational(c['F_interval']['upper']) for c in x['cases'])
x=read('Herglotz-truncation-results.json')
# These finite records are asymptotic diagnostics, not tests of a universal theorem.
diagnostic_records=dict(transition=len(x['transition_checks']),remainder=len(x['remainder_checks']),quadrature=len(x['independent_gamma_quadrature_checks']))
outcomes['Herglotz-quadrature']=all(Decimal(c['absolute_residual'])<Decimal('1e-40') for c in x['independent_gamma_quadrature_checks'])
result=dict(changed_sources=changed,changed_dependencies=changed_dependencies,pdf_sha256=pdfhash,
 pdf_matches_build=pdfhash==build['pdf_sha256'],pdf_matches_render=pdfhash==render['pdf_sha256'],
 page_count=render['page_count'],source_documents=doc['source_documents'],converged_build=build['passed'],
 pdf_static_checks=render['static_passed'],document_integrity=doc['passed'],recorded_outcomes=outcomes,
 asymptotic_diagnostic_records=diagnostic_records,
 scope='Recorded evidence integrity only; visual review and scientific replay are separate activities.')
result['passed']=not changed and not changed_dependencies and all(outcomes.values()) and all(result[k] for k in ['pdf_matches_build','pdf_matches_render','converged_build','pdf_static_checks','document_integrity']) and result['page_count']==177 and result['source_documents']==79
(V/'receipt-integrity.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2));raise SystemExit(0 if result['passed'] else 1)
