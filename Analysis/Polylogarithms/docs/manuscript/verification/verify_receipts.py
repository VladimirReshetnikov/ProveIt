"""Verify the integrity and reported outcomes of the committed release evidence.

This reads pinned receipts; it does not rerun mathematics or perform visual QA.
"""
from pathlib import Path
from fractions import Fraction
from decimal import Decimal
import hashlib, json, sys, subprocess
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
for part in ['14','16','17','18','19','19b']:
    x=read(f'gaussian-replay/{part}/replay-summary.json')
    outcomes['gaussian-replay/'+part]=x['all_programs_exited_zero']
x=read('gaussian-replay/14/shuffle_verification.json')
outcomes['gaussian-shuffle']=x['status']=='PASS' and x['normal_forms_reexpanded']==511 and x['bigraded_sectors_checked']==45
x=read('gaussian-replay/14/exact-summary.json')
outcomes['gaussian-ladders-and-cubic']=x['ladders']['passed']==35 and x['cubic_reference_reproduced_exactly']
x=read('gaussian-replay/16/verification.json')
outcomes['gaussian-Chebyshev']=x['total_interval_certificates']==89 and x['counts']['independent_high_precision_quadratures']==8
x=read('gaussian-replay/17/rational_certificates.json')
outcomes['gaussian-midpoint']=len(x['certificates'])==6
x=read('gaussian-replay/18/verification_summary.json')
outcomes['signed-Euler']=x['status']=='PASS' and x['total_check_cases']==588
x=read('gaussian-replay/19/verification_summary.json');r=read('gaussian-replay/19/replay_summary.json')
outcomes['Holder-values']=x['rational_value_certificates']==75 and r['count']==75 and all(c['center_equal'] and c['radius_equal'] for c in r['checks'])
x=read('gaussian-replay/19b/sixth_root_checks.json')
outcomes['sixth-root-one-two']=x['comparison_count']==56 and x['explicit_example_count']==4
x=read('Herglotz-truncation-results.json')
# These finite records are asymptotic diagnostics, not tests of a universal theorem.
diagnostic_records=dict(transition=len(x['transition_checks']),remainder=len(x['remainder_checks']),quadrature=len(x['independent_gamma_quadrature_checks']))
outcomes['Herglotz-quadrature']=all(Decimal(c['absolute_residual'])<Decimal('1e-40') for c in x['independent_gamma_quadrature_checks'])
archive_errors=[]
archives=read('incoming-archives.json')+read('research-incoming-archives.json')
for archive in archives:
    p=B.parents[3]/archive['archive']
    blob=p.read_bytes() if p.is_file() else subprocess.check_output(['git','show',archive['archive_git_revision']+':'+archive['archive']],cwd=B.parents[3])
    if hashlib.sha256(blob).hexdigest()!=archive['archive_sha256']:
        archive_errors.append(archive['archive'])
    for member in archive['files']:
        p=B.parent/member['path']
        if not p.is_file() or digest(p,False)!=member['sha256']:
            archive_errors.append(member['path'])
outcomes['incoming-archive-preservation']=len(archives)==11 and sum(len(a['files']) for a in archives)==441 and not archive_errors
for part,count in [('rigidity',1),('distribution',7),('conductor',4),('complement',5),('reflection',8)]:
    x=read(f'incoming-replay/{part}/replay-summary.json')
    outcomes['incoming-replay/'+part]=x['passed'] and len(x['commands'])==count and all(c['exit_code']==0 for c in x['commands']) and all((V/'incoming-replay'/part/p).is_file() for p in x['fresh_result_files'])
x=read('incoming-replay/rigidity/results/S4_verification.json')
outcomes['S4-exact-certificate']=x['verified'] and x['residual_terms']==0 and x['duality_relations']==1 and x['standard_relations']==911 and x['relation_counts']=={'ds':713,'lift':17,'regularized_ds':181}
x=read('incoming-replay/rigidity/results/ladder_certificates.json')
outcomes['complement-classification']=x['status']=='all checks passed' and x['check_count']==2012 and x['trinomial_survey']['exact_quotient_irreducibility_checks']==435
x=read('incoming-replay/rigidity/results/reflected_exact.json')
outcomes['reflected-exact']=x['status']=='passed' and x['exact_assertions']==119
x=read('incoming-replay/distribution/data/exact_summary.json')
outcomes['distribution-incoming']=x['all_checks_passed'] and x['rank_cases']==295 and x['normal_form_cases']==295 and x['maximum_q']==60
x=read('incoming-replay/conductor/certificates/exact_checks.json')
outcomes['conductor-incoming']=x['all_passed'] and x['q12_normal_form'] and all(len(x[k])==n and all(c['passed'] for c in x[k]) for k,n in [('rank_checks',295),('composite_checks',29),('jet_checks',18)])
x=read('incoming-replay/conductor/certificates/trace_coefficients.json')
outcomes['trace-coefficients']=x['all_passed'] and len(x['principal_checks'])==6 and x['chi4_level260']['passed']
x=read('incoming-replay/complement/certificates/exact_report.json')
outcomes['complement-depth-exact']=x['status']=='PASS' and all(x['checks'][k]==n for k,n in [('trailing_zero_reexpansions',511),('one_zero_independent_matches',66),('two_zero_independent_matches',10),('high_depth_catalogue_entries',142),('lyndon_triangular_checks',1023)])
x=read('incoming-replay/complement/certificates/certificate_replay_report.json')
outcomes['complement-independent-replay']=x['status']=='PASS' and x['catalogue_entries_replayed']==142 and x['rational_component_width_checks']==6
x=read('incoming-replay/reflection/data/relation_space_certificates.json')
outcomes['restricted-relation-spaces']=len(x['checks'])==30 and all(c['nullity']==c['predicted_nullity'] for c in x['checks'])
x=read('incoming-replay/reflection/data/s6_rational_certificate.json')
r=x['integer_normalized_residual_interval']
outcomes['S6-residual-enclosure']=x['euler_terms']==900 and x['residual_interval_contains_zero'] and Decimal(r['lower'])<=0<=Decimal(r['upper']) and max(abs(Decimal(r['lower'])),abs(Decimal(r['upper'])))<Decimal('1e-260') and x['coefficients']==[485683200,-665395200,-36864000,401080320,-258247,11750400,109347840,971366400]
x=read('incoming-native-results.json')
outcomes['incoming-native']=x['all_pass'] and len(x['checks'])==5
x=read('reflected-sharp-results.json')
outcomes['reflected-sharp-diagnostics']=x['all_pass'] and len(x['checks'])==9 and all(c['passed'] for c in x['checks'])
for part,count in [('rank',2),('cm-zero',1),('formal',1),('angular',1),('cayley',4),('lerch',2)]:
    x=read(f'research-replay/{part}/replay-summary.json')
    outcomes['research-replay/'+part]=x['passed'] and len(x['commands'])==count and all(c['exit_code']==0 for c in x['commands'])
x=read('higher-zero-certificates.json')
outcomes['higher-zero-primary']=x['status']=='PASS' and x['root_endpoint_enclosures']==90 and x['critical_interval_enclosures']==36 and x['counts']['6']['counts_before_and_at_threshold']==[4,4,4,6] and x['counts']['7']['counts_before_and_at_threshold']==[5,5,5,5,7]
x=read('higher-zero-independent.json')
outcomes['higher-zero-independent']=x['status']=='PASS' and x['endpoint_checks']==90 and x['critical_interval_checks']==36 and all(c['sign']!=0 for c in x['checks']) and x['input_sha256']==digest(V/'higher-zero-certificates.json',False)
x=read('research-native-results.json')
outcomes['research-native']=x['all_pass'] and len(x['checks'])==3
x=read('research-replay/angular/fresh-receipt.json')
outcomes['S2-exact-and-independent']=x['reference_data_unchanged'] and all(c['status']=='pass' for c in x['checks']) and x['checks'][1]['result']['exact_target_verified'] and x['checks'][1]['result']['rows']==25 and all(c['pass'] for c in x['checks'][2]['result'])
x=read('research-replay/rank/data/verification_report.json')
outcomes['all-weight-rank-replay']=x['status']=='PASS' and x['rank_weights']==40 and x['rank_max']==41 and x['even_formula_count']==210 and x['affine_row_checks']==816 and x['gaussian_membership_checks']==420
x=json.loads((B.parent/'reports/cayley-s4-continuation/data/S8_exclusion_N1000.json').read_text())
outcomes['S8-frozen-vector-exclusion']=x['N']==1000 and not x['contains_zero'] and Fraction(x['residual']['upper'])<0 and Fraction(x['residual']['upper'])-Fraction(x['residual']['lower'])<Fraction('2.080e-290')
x=read('S6-coordinate-change.json')
outcomes['S6-coordinate-equivalence']=x['status']=='PASS' and x['residual_terms']==0 and x['standard_rows']==[[2,5],[3,4]]
visual=read('visual-review.json')
outcomes['recorded-visual-review']=visual['passed'] and visual['pdf_sha256']==pdfhash and visual['page_count']==298 and visual['all_contact_sheets_reviewed']==19 and visual['scientific_figures_reviewed']==9 and not visual['findings']
result=dict(changed_sources=changed,changed_dependencies=changed_dependencies,pdf_sha256=pdfhash,
 pdf_matches_build=pdfhash==build['pdf_sha256'],pdf_matches_render=pdfhash==render['pdf_sha256'],
 page_count=render['page_count'],source_documents=doc['source_documents'],converged_build=build['passed'],
 pdf_static_checks=render['static_passed'],document_integrity=doc['passed'],recorded_outcomes=outcomes,
 asymptotic_diagnostic_records=diagnostic_records,incoming_archive_errors=archive_errors,
 scope='Recorded evidence integrity only; visual review and scientific replay are separate activities.')
result['passed']=not changed and not changed_dependencies and all(outcomes.values()) and all(result[k] for k in ['pdf_matches_build','pdf_matches_render','converged_build','pdf_static_checks','document_integrity']) and result['page_count']==298 and result['source_documents']==248 and render.get('pdf_author')=='ProveIt Contributors'
(V/'receipt-integrity.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2));raise SystemExit(0 if result['passed'] else 1)
