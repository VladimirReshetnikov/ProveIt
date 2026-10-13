"""Verify the integrity and reported outcomes of the committed release evidence.

This reads pinned receipts; it does not rerun mathematics or perform visual QA.
"""
from pathlib import Path
from fractions import Fraction
from decimal import Decimal
import hashlib, json, sys, subprocess, io, zipfile
import re
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
archives=sum((read(name) for name in ['incoming-archives.json',
    'research-incoming-archives.json','third-incoming-archives.json',
    'fourth-incoming-archives.json','fifth-incoming-archives.json',
    'sixth-incoming-archives.json','seventh-incoming-archives.json',
    'eighth-incoming-archives.json','ninth-incoming-archives.json','tenth-incoming-archives.json','eleventh-incoming-archives.json','twelfth-incoming-archives.json','thirteenth-incoming-archives.json','fourteenth-incoming-archives.json','fifteenth-incoming-archives.json','sixteenth-incoming-archives.json','seventeenth-incoming-archives.json','eighteenth-incoming-archives.json','nineteenth-incoming-archives.json','twentieth-incoming-archives.json','twenty-first-incoming-archives.json','twenty-second-incoming-archives.json','twenty-third-incoming-archives.json','twenty-fourth-incoming-archives.json','twenty-fifth-incoming-archives.json']), [])
for archive in archives:
    p=B.parents[3]/archive['archive']
    blob=p.read_bytes() if p.is_file() else subprocess.check_output(['git','show',archive['archive_git_revision']+':'+archive['archive']],cwd=B.parents[3])
    if hashlib.sha256(blob).hexdigest()!=archive['archive_sha256']:
        archive_errors.append(archive['archive'])
    with zipfile.ZipFile(io.BytesIO(blob)) as preserved_zip:
        for opaque in archive.get('archive_only_members',[]):
            if opaque['member'] not in preserved_zip.namelist():archive_errors.append(opaque['member'])
    for member in archive['files']:
        p=B.parent/member['path']
        if not p.is_file() or digest(p,False)!=member['sha256']:
            archive_errors.append(member['path'])
outcomes['incoming-archive-preservation']=len(archives)==137 and sum(len(a['files']) for a in archives)==4861 and not archive_errors
x=read('incoming-retirement.json')
archive_by_path={a['archive']:a for a in archives}
outcomes['imported-archive-retirement']=x['archive_count']==16 and x['preserved_members']==691 and len(x['archives'])==16 and sum(a['members'] for a in x['archives'])==691 and (B.parents[3]/'docs/incoming/README.md').is_file() and all(
    not (B.parents[3]/a['archive']).exists() and a['all_members_match_placement_blobs'] and a['archive'] in archive_by_path and a['arrival_commit']==archive_by_path[a['archive']]['archive_git_revision'] and a['members']==len(archive_by_path[a['archive']]['files']) and (B.parents[3]/a['destination']).is_dir() for a in x['archives'])
x=read('fifth-incoming-retirement.json')
outcomes['fifth-archive-retirement']=x['archive_count']==5 and x['preserved_members']==178 and len(x['archives'])==5 and sum(a['members'] for a in x['archives'])==178 and all(
    not (B.parents[3]/a['archive']).exists() and a['all_members_match_placement_blobs'] and a['archive'] in archive_by_path and a['arrival_commit']==archive_by_path[a['archive']]['archive_git_revision'] and a['members']==len(archive_by_path[a['archive']]['files']) for a in x['archives'])
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
for batch,parts in [('third', [('herglotz',2),('phase',2),('uniform',1),('boundary',4),('signed',1)]),
                    ('fourth', [('jets',3),('integral',6),('fractional',1),('threshold',1),('golden',2)])]:
    for part,count in parts:
        x=read(f'{batch}-replay/{part}/replay-summary.json')
        outcomes[f'{batch}-replay/{part}']=x['passed'] and len(x['commands'])==count and all(
            c['exit_code']==0 for c in x['commands']) and bool(x['fresh_result_files']) and all(
            (V/f'{batch}-replay'/part/p).is_file() for p in x['fresh_result_files'])
x=read('CM-native-results.json')
outcomes['CM-native']=x['all_pass'] and x['working_precision']==90 and x['q_terms']==100 and len(x['checks'])==25 and all(c['passed'] for c in x['checks'])
x=read('CM-nonvanishing.json')
outcomes['CM-rational-nonvanishing']=x['status']=='PASS' and len(x['rows'])==2 and x['uniform_principal_lower_bound']=='7/20' and all(
    c['passed'] and Fraction(c['total_bound'])<Fraction(c['asserted_upper']) for c in x['rows'])
x=read('CM-genus-extensions.json')
outcomes['CM-genus-extensions']=x['status']=='PASS' and len(x['new_ratio_formulas'])==9 and len(x['lattice_bounds'])==5 and all(c['passed'] for c in x['new_ratio_formulas']) and all(Fraction(c['total_bound'] if c['power']==4 else c['nonunit_tail'])<Fraction(c['upper']) for c in x['lattice_bounds'])
x=read('CM-single-Weber.json')
outcomes['CM-single-and-Weber']=x['status']=='PASS' and len(x['class_number_one_certificates'])==2 and all(c['certificate']['certified_by_integrality'] for c in x['class_number_one_certificates']) and x['weber23_cubing_resultant_exact'] and x['weber39_irreducibility_witness']['degree']==12
x=read('CM-Weber-independent.json')
outcomes['CM-Weber-independent']=x['status']=='PASS' and x['prime']==5 and x['degree']==12 and x['final_frobenius_residue']==[0,1] and len(x['proper_divisor_checks'])==2
x=read('CM-genus-plot.json')
outcomes['CM-plot-diagnostic']=len(x['rows'])==80 and Decimal(x['first_ratio_exact_comparison_residual'])<Decimal('1e-7')
x=read('research-replay/cm-zero/replay/modular_weight_polynomials.json')
outcomes['CM-modular-polynomial-certificates']=len(x['results'])==11 and all(c['F_monic'] and c['F_degree']==c['weight'] and c['cleared_identity_certificate']['all_exact_residuals_zero'] for c in x['results'])
x=read('research-replay/cm-zero/replay/verify_genus_arithmetic_receipt.json')
outcomes['CM-genus-seed-arithmetic']=x['number_of_equalities']==6 and len(x['checks'])==6 and all(c['equality_verified_exactly'] and c['candidate_verified_positive_exactly'] for c in x['checks'])
x=read('research-replay/cm-zero/replay/cm_norms_receipt.json')
outcomes['CM-class-polynomial-intervals']=len(x['class_polynomial_certificates'])==5 and all(c['certified_by_integrality'] for c in x['class_polynomial_certificates'])
x=read('research-replay/cm-zero/replay/cm_genus_receipt.json')
outcomes['CM-genus-factors-and-roots']=len(x['exact_and_interval_certificates'])==3 and all(c['factorization_verified_exactly'] and c['cubic_identity_verified_exactly'] and c['square_identity_verified_exactly'] for c in x['exact_and_interval_certificates'])
x=read('S8-coordinate-check.json')
outcomes['new-S8-vector-coordinates']=x['status']=='PASS' and x['gcd']==1 and x['normalized_rhs_coefficients']==[str(-Fraction(c,x['primitive_vector'][0])) for c in x['primitive_vector'][1:]]
x=read('third-replay/signed/results/replay_summary.json')
outcomes['new-S6-S8-proximity-replay']=len(x['checks'])==4 and all(c['status']=='passed' for c in x['checks']) and all(c.get('identities_proved',False)==False for c in x['checks']) and x['checks'][-1]['normalized_bound_exponent']==355
x=read('multivariable-distribution-results.json')
outcomes['multivariable-distribution-raw-ranks']=x['status']=='PASS' and x['cases']==210 and len(x['checks'])==210 and x['corruption_controls']==1 and all(c['passed'] and c['reflected_dimension']==c['expected'] for c in x['checks'])
x=read('final-raster-equivalence.json')
outcomes['historical-340-page-raster-equivalence']=x['pdf_sha256']=='0c27415b8024aa8448b46cc5b95197454b170c2a249e0c86d82e41e871bf845e' and x['page_count']==340 and x['thumbnail_pages_compared']==340 and x['raster_files_compared']==432 and x['all_rasters_identical']
# This historical receipt never establishes review of the expanded current PDF.
x=read('subcritical-difference-certificates.json')
outcomes['subcritical-exact-signs']=x['status']=='PASS' and x['integer_root_inequalities']==3064 and x['difference_sign_certificates']==616 and x['Euler_increment_signs']==112 and len(x['signs'])==616 and all(0<Fraction(c['lower'])<=Fraction(c['upper']) for c in x['signs'])
outcomes['subcritical-Gaussian-enclosures']=len(x['Gaussian_cases'])==7 and all(c['passed'] and c['Euler_terms']==192 and Fraction(c['analytic_Gaussian_interval']['lower'])<Fraction(c['analytic_Gaussian_interval']['upper'])<0 and Fraction(c['width'])==Fraction(c['analytic_Gaussian_interval']['upper'])-Fraction(c['analytic_Gaussian_interval']['lower']) and c['rational_error_constant']==('5/4' if c['a']=='0' and c['b']=='3/2' else '57/50') for c in x['Gaussian_cases'])
axis=next(c for c in x['Gaussian_cases'] if c['a']=='0' and c['b']=='3/2')
outcomes['Gaussian-axis-exact-comparison']=-2*Fraction(axis['analytic_Gaussian_interval']['upper'])>Fraction(227,200)
x=read('subcritical-native-results.json')
outcomes['subcritical-native']=x['all_pass'] and x['working_precision']==100 and len(x['checks'])==7 and all(c['within_exact_interval'] for c in x['checks'])
for part,count in [('threshold',3),('geometry',1),('boundary',1)]:
    x=read(f'real-order-replay/{part}/replay-summary.json')
    outcomes['real-order-replay/'+part]=x['passed'] and len(x['commands'])==count and all(c['exit_code']==0 for c in x['commands']) and bool(x['fresh_result_files']) and all((V/'real-order-replay'/part/p).is_file() for p in x['fresh_result_files'])
x=read('real-order-replay/threshold/data/exact_certificates.json')
outcomes['real-order-fractional-certificates']=x['all_checks_passed'] and len(x['euler'])==8 and len(x['angle_brackets'])==12 and x['integer_root_inequalities_checked']==7430
x=read('real-order-replay/threshold/data/diagnostics.json')
outcomes['real-order-symbolic-identities']=len(x['symbolic_checks'])==9 and all(x['symbolic_checks'].values())
x=read('real-order-replay/geometry/data/geometry_diagnostics.json')
outcomes['real-order-geometry-diagnostics']=x['status']=='all diagnostic assertions passed' and len(x['direct_kernel_comparisons'])==9 and len(x['zero_arcs'])==16
x=read('real-order-replay/boundary/data/geometry_boundary_diagnostics.json')
outcomes['real-order-boundary-diagnostics']=x['status']=='all diagnostic assertions passed' and x['precision_decimal_digits']==90 and len(x['rows'])==21
x=read('Gaussian-axis-plot.json')
outcomes['Gaussian-axis-plot-diagnostic']=x['working_precision']==40 and len(x['points'])==180
x=read('axis-wording-raster-comparison.json')
outcomes['historical-axis-wording-raster-review']=x['pdf_sha256']=='3f9a6a957e932c9c6d0351c32c705dca61f5f391462f9ccf255d5fc06f21eb5f' and x['previous_pdf_sha256']=='b416e14735a4c3aeba8fcac288673846ef12a41125f5e11936b185be85159afd' and x['page_count']==379 and x['thumbnail_pages_compared']==379 and x['changed_thumbnail_pages']==[165] and x['contact_sheets_compared']==24 and x['changed_contact_sheets']==[161] and x['changed_full_pages']==[165]
x=read('mellin-domain-raster-comparison.json')
outcomes['historical-Mellin-domain-raster-review']=x['pdf_sha256']=='71f50bc5bc15a3bbb0c2793bf98efe4a15c46440ca9951f919cabb2d5b03ea73' and x['previous_pdf_sha256']=='3f9a6a957e932c9c6d0351c32c705dca61f5f391462f9ccf255d5fc06f21eb5f' and x['page_count']==379 and x['thumbnail_pages_compared']==379 and x['changed_thumbnail_pages']==[142] and x['contact_sheets_compared']==24 and x['changed_contact_sheets']==[129] and x['changed_full_pages']==[142]
for part,count in [('beta',4),('compensated',4),('critical',3),('extremal',1),('harmonic',1)]:
    x=read(f'fifth-replay/{part}/replay-summary.json')
    outcomes['fifth-replay/'+part]=x['passed'] and len(x['commands'])==count and all(c['exit_code']==0 for c in x['commands']) and bool(x['fresh_result_files']) and all((V/'fifth-replay'/part/p).is_file() for p in x['fresh_result_files'])
x=read('fifth-replay/extremal/results/replay_summary.json')
outcomes['fifth-extremal-exact-suite']=x['all_passed'] and not x['diagnostics_requested'] and len(x['checks'])==5 and all(c['returncode']==0 for c in x['checks'])
x=read('fifth-replay/extremal/results/gaussian_envelope_certificate.json')
outcomes['Gaussian-maximum-exact-enclosure']=x['decimal_grid_digits']==90 and x['euler_terms']==160 and x['certified_sign_tests']==4 and x['root_decimal_enclosure']==['1.30221658710124120959237170','1.30221658710124120959237171'] and x['maximum_enclosure']==['1.136561103339509560952586375779942387681723540','1.136561103339509560952586375779942387681723541'] and 0<Fraction(x['derivative_at_left'][0])<=Fraction(x['derivative_at_left'][1]) and Fraction(x['derivative_at_right'][0])<=Fraction(x['derivative_at_right'][1])<0 and Fraction(x['maximum_enclosure'][1])<Fraction(57,50)
x=read('universal-Euler-certificates.json')
outcomes['universal-Euler-finite-kernel-checks']=x['status']=='PASS' and x['kernel_grid_cases']==7581 and x['power_grid_cases']==12369 and x['kernel_equality_cases']==19 and x['quadratic_optimum_equalities']==19 and x['exact_tail_normalizations']==560 and x['coefficient_corruption_controls']==1 and len(x['kernel_rows'])==19 and all(Fraction(c['minimum_strict_slack'])>0 for c in x['kernel_rows'])
outcomes['universal-Euler-exact-enclosures']=x['integer_root_inequalities']==2552 and x['Euler_increment_signs']==352 and x['scaled_tail_enclosures']==66 and len(x['Gaussian_cases'])==11 and all(c['passed'] and c['Euler_terms']==160 and c['rational_error_constant']=='5/4' and Fraction(c['Gaussian_interval']['lower'])<Fraction(c['Gaussian_interval']['upper'])<0 and len(c['tails'])==6 and all(0<Fraction(t['scaled_error_interval']['lower'])<Fraction(t['scaled_error_interval']['upper']) and (t['upper_below_axis_lower'] or (c['a']=='0' and t['N']==1)) for t in c['tails']) for c in x['Gaussian_cases'])
x=read('universal-Euler-native.json')
outcomes['universal-Euler-native-diagnostics']=x['all_pass'] and x['working_precision']==90 and len(x['checks'])==11 and all(c['within_exact_interval'] and len(c['tails'])==6 and all(t['within_exact_interval'] for t in c['tails']) for c in x['checks'])
x=read('fifth-replay/beta/data/exact_certificates.json')
outcomes['fifth-beta-certificates']=x['status']=='PASS' and x['root_inequalities_checked']==1755 and len(x['values'])==12
x=read('fifth-replay/beta/data/symbolic_checks.json')
outcomes['fifth-beta-symbolic']=x['status']=='PASS' and x['number_of_exact_checks']==176 and len(x['checks'])==176
x=read('fifth-replay/critical/data/exact_certificates.json')
outcomes['fifth-critical-certificates']=x['status']=='PASS' and x['root_acceptance_inequalities_checked']==2555 and len(x['rows'])==5 and Fraction(x['R128_half_minus_quarter']['lower'])>0
x=read('fifth-replay/extremal/results/s6/verification_receipt.json')
outcomes['fifth-S6-prescribed-span-separator']=x['result']=='PASS' and x['rows_verified']==5131 and x['ambient_coordinates']==2546 and int(x['target_pairing'])!=0 and x['complete_family_reenumeration']=='PASS'
x=read('fifth-replay/extremal/results/cyclic_prime_results.json')
outcomes['fifth-cyclic-raw-Smith-checks']=x['all_passed'] and x['verified_cases']==52 and len(x['checks'])==52
x=read('fifth-replay/harmonic/logs/verification_run.json')
outcomes['fifth-harmonic-default-suite']=len(x['checks'])==4 and all(c['exit_code']==0 for c in x['checks']) and not x['requested_full_harmonic_numerics']

for batch, parts in [('sixth', {'all-depth':1,'radial':5,'sharp':4,'golden':1,'uniform-bounds':1,'uniform-continuation':1}),
                     ('seventh', {'lambert':1,'large-orders':1,'leading-one':2,'tetra':1,'extremizers':1}),
                     ('eighth', {'resonance':1,'shifted':2,'algebra':3,'closure':4,'calculus':1}),
                     ('ninth', {'gauss':2,'mellin':9,'nested':1,'critical':1,'harmonic':1}),
                     ('tenth', {'endpoint':3,'twisted':1}),
                     ('eleventh', {'coincident':2,'dougall':2,'identities':1,'transport':2,'jets':1,'triple':2}),
                     ('twelfth', {'directional':1,'mixed':1,'ordered':5,'collisions':2,'contact':2})]:
    for part,count in parts.items():
        x=read(f'{batch}-replay/{part}/replay-summary.json')
        folder=B.parent/'reports'/x['source_folder']
        outcomes[f'{batch}-replay/'+part]=(x['passed'] and len(x['commands'])==count and
            all(c['exit_code']==0 for c in x['commands']) and
            all((V/f'{batch}-replay'/part/p).is_file() for p in x['fresh_result_files']) and
            all(digest(folder/p,False)==h for p,h in x['source_code_sha256'].items()))
    x=read(f'{batch}-incoming-retirement.json')
    outcomes[batch+'-archive-retirement']=(x['archive_count']==len(parts) and
        len(x['archives'])==len(parts) and x['preserved_members']==sum(a['members'] for a in x['archives']) and
        all(a['retired'] and not (B.parents[3]/a['archive']).exists() and
            a['arrival_commit']==archive_by_path[a['archive']]['archive_git_revision'] and
            a['members']==len(archive_by_path[a['archive']]['files']) for a in x['archives']))
x=read('sixth-replay/radial/certificates/global_verified.json')
outcomes['sixth-full-radial-cover']=x['status']=='PASS' and x['full_cover'] and x['start']==0 and x['stop']==2304 and x['cells_verified']==2304 and x['root_boxes_verified']==4609
x=read('seventh-replay/leading-one/reproduction/exact/exact-results.json')
outcomes['leading-one-exact']=x['status']=='PASS' and x['counts']=={'odd_central_moment_signs':180,'halfshift_coefficient_equalities':768,'positive_shift_coefficient_equalities':960,'local_coefficient_equalities':30,'certified_root_brackets':18}
x=read('seventh-replay/leading-one/reproduction/symbolic/symbolic-results.json')
outcomes['leading-one-symbolic']=x['status']=='PASS' and len(x['checks'])==5
x=read('seventh-replay/tetra/code/tetralogarithm_receipt.json')
outcomes['tetralogarithm-exact-descent']=x['status']=='PASS' and x['rows']==42 and x['tensor_coordinates']==230 and not x['nonzero_tensor_residual'] and x['matches_conjecture_exactly'] and x['general_functional_identity_exact']
x=read('tetralogarithm-table-audit.json')
outcomes['printed-tetralogarithm-independent-audit']=x['status']=='PASS' and x['printed_rows_checked']==42 and x['ordered_tensor_residual_coordinates']==0 and x['corrupted_first_coefficient_nonzero_coordinates']==12 and x['retains_rational_prime_two']
x=read('seventh-replay/extremizers/verification/replay_report.json')
outcomes['seventh-extremizer-finite-suite']=x['status']=='passed' and not x['diagnostics_requested'] and len(x['scripts'])==4 and all(c['status']=='passed' and c['return_code']==0 for c in x['scripts'])
x=read('seventh-final-raster-comparison.json')
outcomes['historical-seventh-final-raster-review']=x['pdf_sha256']=='15725fcab0ef5baeff68dc0fcb14eaf1da93a4906ad0a8ef68423cb46dd250db' and x['previous_pdf_sha256']=='839a763e832960fec3728797bb5de9b86a671836358ae844659e523686f9d54f' and x['page_count']==392 and x['thumbnail_pages_compared']==392 and x['contact_sheets_compared']==25 and x['changed_thumbnail_pages']==[2,37,156] and x['changed_contact_sheets']==[1,33,145] and x['changed_full_pages']==[2,37,156]
x=read('stieltjes-radial-certificates.json')
outcomes['strict-Stieltjes-radial-exact-controls']=x['status']=='PASS' and x['symbolic_identities']==3 and x['corrupted_polynomial_controls']==1 and x['counts']=={'atomic_pair_equalities':200,'quantitative_bounds':200,'strict_positive_cases':175,'constant_zero_cases':25,'prescribed_outside_radius_counterexamples':200}
x=read('stieltjes-radial-native.json')
outcomes['strict-Stieltjes-radial-native']=x['all_pass'] and len(x['checks'])==4 and all(x['checks'].values())
x=read('logistic-resolvent-results.json')
outcomes['logistic-resolvent-exact-controls']=x['status']=='PASS' and x['exact_confluent_coefficient_identities']==117 and x['exact_partial_fraction_identities']==6 and x['printed_base_polynomials']==3 and x['printed_quartic_moment'] and x['printed_real_second_moments']==2 and x['corruption_controls']==1
outcomes['logistic-resolvent-numerical-diagnostics']=x['numerical_diagnostics']['working_decimal_digits']==65 and not x['numerical_diagnostics']['interval_certified'] and len(x['numerical_diagnostics']['cases'])==30 and all(Decimal(c['absolute_residual'])<Decimal('1e-55') for c in x['numerical_diagnostics']['cases'])
x=read('logistic-resolvent-native.json')
outcomes['logistic-resolvent-native']=x['all_pass'] and x['all_exact_pass'] and x['exact_coefficient_identities']==45 and not x['numerical_diagnostics']['interval_certified'] and len(x['numerical_diagnostics']['rows'])==6 and all(c['passed'] for c in x['numerical_diagnostics']['rows'])
x=read('sixth-replay/all-depth/data/verification_report.json')
outcomes['all-depth-finite-exact-suite']=x['status']=='PASS' and x['total_checked_assertion_groups']==5713
x=read('all-depth-final-raster-comparison.json')
outcomes['historical-all-depth-final-raster-review']=x['pdf_sha256']=='abb118011a57790f16c1c4391de82bd6b19ad0fd4480c34e317a9316ec94dc4c' and x['previous_pdf_sha256']=='97a74937fa354d400503053fc7269436b6740e6cf097b71c5a2b227518e5a2eb' and x['page_count']==417 and x['thumbnail_pages_compared']==417 and x['contact_sheets_compared']==27 and x['changed_thumbnail_pages']==[181,197] and x['changed_contact_sheets']==[177,193] and x['changed_full_pages']==[181,197]
x=read('eighth-replay/algebra/verification/exact_results.json')['exact']
outcomes['Stieltjes-convolution-exact']=x['status']=='passed' and x['assertion_count']==229 and len(x['assertions'])==229
for dps in [40,50]:
    x=read(f'eighth-replay/algebra/verification/numeric_results_{dps}dps.json')['numerical']
    outcomes[f'Stieltjes-convolution-{dps}-digit-diagnostics']=x['status']=='passed' and x['decimal_precision']==dps and len(x['checks'])==31
x=read('eighth-replay/shifted/data/exact_identities.json')
outcomes['shifted-Stieltjes-finite-coefficients']=len(x['identities'])==28 and len(x['contact_coefficients'])==8
x=read('eighth-replay/shifted/data/numerical_validation.json')
outcomes['shifted-Stieltjes-full-diagnostics']=x['status']=='all passed' and x['working_decimal_precision']==50 and len(x['checks'])==64
x=read('eighth-replay/closure/results/exact_verification.json')
outcomes['bilinear-Stieltjes-exact']=x['status']=='PASS' and x['rows']==45 and x['exact_checks']==272 and x['max_total']==8
for name,count in [('numeric_verification',19),('stieltjes_pair_verification',3)]:
    x=read(f'eighth-replay/closure/results/{name}.json')
    outcomes[name]=x['status']=='PASS' and x['dps']==45 and x['number_of_checks']==count and len(x['checks'])==count
x=read('eighth-replay/calculus/verification/exact_coefficients.json')
outcomes['Stieltjes-calculus-exact']=x['exact_assertions']==60 and len(x['identities'])==15
x=read('eighth-replay/calculus/verification/exact_jet_polynomials.json')
outcomes['Stieltjes-calculus-jet-polynomials']=x['all_exact_checks_passed'] and len(x['first_jet'])==10 and len(x['second_jet_p0_r2'])==8 and len(x['bernoulli_p0_r0'])==7
x=read('eighth-replay/resonance/data/replay_all.json')
outcomes['resonance-full-four-suites']=len(x['runs'])==4 and {r['suite'] for r in x['runs']}=={'exact','resonance','gamma','herglotz'} and all(r['status']=='passed' for r in x['runs'])
x=read('eighth-replay/resonance/data/nonseparable_jets_checks.json')
outcomes['nonseparable-finite-ring-exact']=x['status']=='all assertions passed' and x['arithmetic']=='exact F_2 bit elimination' and len(x['cases'])==3
x=read('stieltjes-dilation-results.json')
outcomes['Stieltjes-dilation-exact-controls']=x['status']=='PASS' and x['exact_counts']=={'generator_trace':9,'derivative_trace':72,'covering_constant_terms':63,'trace_constant_terms':63,'trace_composition':9,'polygamma_specializations':8} and x['corruption_controls']==1
diag=x['numerical_diagnostics']
outcomes['Stieltjes-dilation-diagnostics']=diag['working_decimal_digits']==60 and not diag['interval_certified'] and len(diag['cases'])==15 and sum(c['kind']=='raw-trace-Fourier-integral' for c in diag['cases'])==10 and all(Decimal(c['absolute_residual'])<Decimal('1e-50' if c['kind']=='raw-trace-Fourier-integral' else '1e-25') for c in diag['cases'])
x=read('stieltjes-correlation-native.json')
outcomes['Stieltjes-native-exact-and-diagnostics']=x['all_pass'] and x['all_exact_pass'] and x['exact_generator_trace_checks']==6 and x['exact_derivative_trace_checks']==30 and x['numerical_diagnostics']['working_precision']==70 and not x['numerical_diagnostics']['interval_certified'] and len(x['numerical_diagnostics']['rows'])==4 and all(c['passed'] for c in x['numerical_diagnostics']['rows'])
x=read('ninth-replay/gauss/results/exact_checks.json')
outcomes['Gauss-Hurwitz-exact']=x['status']=='PASS' and x['exact_check_count']==512 and len(x['checks'])==512
x=read('ninth-replay/gauss/results/numerical_checks.json')
outcomes['Gauss-Hurwitz-diagnostics']=x['status']=='PASS' and x['diagnostic_count']==64 and x['working_decimal_digits']==65 and Decimal(x['largest_scaled_error'])<Decimal('1e-40')
x=read('ninth-replay/nested/results/exact_verification.json')
outcomes['nested-harmonic-exact']=x['status']=='PASS' and x['assertions']==826 and len(x['checks'])==826
for name,count in [('numeric_verification',99),('higher_jet_verification',960),('cyclotomic_verification',16)]:
    x=read(f'ninth-replay/nested/results/{name}.json')
    outcomes['nested-'+name]=x['status']=='PASS' and x['checks']==count and len(x['rows'])==count and x['precision_decimal_digits']==60 and Decimal(x['max_scaled_residual'])<Decimal('1e-42')
x=read('ninth-replay/harmonic/data/exact_coefficients_checks.json')
outcomes['harmonic-triple-exact']=x['all_passed'] and len(x['checks'])==128
x=read('ninth-replay/harmonic/data/harmonic_checks.json')
outcomes['harmonic-rational-kernel-diagnostics']=x['precision_dps']==70 and x['tests']==37 and x['passed']==37
x=read('ninth-replay/harmonic/data/trilinear_checks.json')
outcomes['trilinear-diagnostics']=x['passed'] and x['precision_digits']==42 and x['requested_agreement_digits']==32 and len(x['checks'])==6
x=read('ninth-replay/harmonic/data/gauss_stieltjes_checks.json')
outcomes['Gauss-Stieltjes-mixed-diagnostics']=x['status']=='All numerical and symbolic diagnostics passed.' and x['working_decimal_digits']==75 and x['number_of_mixed_jet_checks']==48 and len(x['mixed_jet_checks'])==48 and Decimal(x['largest_absolute_residual'])<Decimal('1e-50')
x=read('ninth-replay/mellin/results/exact_verification.json')
outcomes['Mellin-dilation-exact']=x['status']=='passed' and x['total_checks']==742
x=read('ninth-replay/mellin/results/verification_summary.json')
outcomes['Mellin-dilation-full-diagnostics']=x['status']=='passed' and x['main_exact_assertions']==742 and x['numerical_comparisons']==77
x=read('ninth-replay/mellin/results/pi_squared_check.json')
outcomes['unequal-dilation-pi-squared-diagnostic']=x['passed'] and x['working_precision']==42 and (x['p'],x['q'],x['r'],x['k'],x['a'])==(2,3,0,1,'1/4') and Decimal(x['absolute_error'])<Decimal('1e-38')
x=read('ninth-replay/critical/verification/depth_projector_verification.json')
outcomes['Cayley-depth-finite-exact']=x['result']=='PASS' and x['consecutive_cut_eulerian_checks']==780 and x['shuffle_multiplicativity_checks']==2150 and len(x['independent_exact_ideal_ranks'])==10
x=read('ninth-replay/critical/verification/s6_oriented_normal_form.json')
outcomes['Cayley-S6-nonzero-formal-normal-form']=x['normal_form_support']==30 and x['max_depth']==2 and len(x['projection'])==30 and x['result']=='NONZERO FORMAL NORMAL FORM; no assertion about the numerical residual'
for name,count in [('translation_results',19),('translation_extensions',6)]:
    x=read(f'ninth-replay/critical/verification/{name}.json')
    outcomes[name]=x['all_passed'] and len(x['records'])==count
x=read('ninth-replay/critical/verification/transition_diagnostics.json')
outcomes['near-critical-full-nine-sample-diagnostics']=len(x['rows'])==9 and x['tighter_replay_L_difference']<1e-9 and 'not certified intervals' in x['status']
x=read('harmonic-gamma-native.json')
outcomes['harmonic-Gamma-native-exact']=x['all_pass'] and x['pure_generator_pass'] and x['mixed_exact_checks']==7 and x['all_mixed_exact_pass'] and x['independent_elementary_integral_pass'] and x['printed_factor_two_rejected']
x=read('tenth-replay/endpoint/results/exact_checks.json')
outcomes['decorated-endpoint-exact']=x['status']=='PASS' and x['exact_assertions']==2600
x=read('tenth-replay/endpoint/results/numerical_checks.json')
outcomes['decorated-endpoint-diagnostics']=x['status']=='PASS' and x['comparisons']==158 and len(x['records'])==158 and x['decimal_precision']==60 and Decimal(x['largest_absolute_error'])<Decimal('1e-50')
x=read('tenth-replay/endpoint/results/endpoint_diagnostics.json')
outcomes['decorated-endpoint-full-arrays']=len(x['rows'])==32 and 'Floating-point endpoint diagnostics' in x['meaning']
x=read('tenth-replay/twisted/verification/replay_run.json')
outcomes['twisted-full-five-script-replay']=x['all_passed'] and x['complete'] and len(x['runs'])==5 and all(r['returncode']==0 for r in x['runs'])
for name,count,precision in [('periodic_calculus_checks',15,50),('twisted_calculus_checks',32,60)]:
    x=read(f'tenth-replay/twisted/data/{name}.json')
    outcomes[name]=x['passed'] and x['working_decimal_precision']==precision and len(x['numerical'])==count
x=read('tenth-replay/twisted/verification/harmonic_coefficients.json')
outcomes['harmonic-Laurent-finite-exact']=x['all_checks_passed'] and len(x['finite_part_derivative_checks'])==30 and len(x['finite_part_reflection_checks'])==30 and len(x['finite_part_primitive_checks'])==30 and len(x['finite_part_multiplication_checks'])==60
x=read('tenth-replay/twisted/verification/harmonic_mellin_numeric.json')
outcomes['harmonic-Laurent-independent-Mellin']=x['all_diagnostics_passed'] and x['decimal_precision']==110 and x['local_series_degrees']==[80,100] and len(x['baseline_checks'])==3 and len(x['laurent_checks'])==4
x=read('tenth-replay/twisted/verification/additional_numeric.json')
outcomes['twisted-additional-integral-diagnostics']=x['status']=='passed' and x['count']==9 and x['decimal_precision']==60 and not x['numerical_proof'] and not x['certified_intervals']
x=read('mixed-twist-results.json')
outcomes['mixed-twist-exact-controls']=x['status']=='PASS' and x['exact_partial_fraction_checks']==64 and x['corruption_controls']==1
outcomes['mixed-twist-independent-diagnostics']=x['numerical_diagnostics']['working_decimal_digits']==60 and not x['numerical_diagnostics']['interval_certified'] and len(x['numerical_diagnostics']['cases'])==25 and all(Decimal(c['absolute_residual'])<Decimal('1e-50') for c in x['numerical_diagnostics']['cases'])
x=read('twisted-mixed-native.json')
outcomes['twisted-mixed-native']=x['all_pass'] and x['all_exact_pass'] and x['exact_partial_fraction_checks']==25 and x['numerical_diagnostics']['working_precision']==70 and not x['numerical_diagnostics']['interval_certified'] and len(x['numerical_diagnostics']['rows'])==9 and all(c['passed'] for c in x['numerical_diagnostics']['rows'])
visual=read('visual-review.json');prior_visual=read('twelfth-visual-review.json')
outcomes['recorded-visual-review']=(visual['passed'] and visual['pdf_sha256']==pdfhash and visual['page_count']==623 and visual['visual_page_coverage']==623 and visual['contact_sheets_reviewed']==0 and visual['scientific_figures_reviewed']==13 and not visual['findings'])
x=read('eleventh-combined-raster-comparison.json')
matched={r['page'] for r in x['exact_matching_page_bodies']};fresh=set(x['changed_page_bodies'])
outcomes['historical-weighted-combined-raster-review-coverage']=(x['pdf_sha256']=='8c78372ceb178cf7b6153269523ee0ea76fef7655cd1ffb4d79f2a4e5a6f7e14' and x['page_count']==463 and x['crop_bottom_points']==57 and x['excluded_content_is_only_page_numbers'] and len(matched)==451 and len(fresh)==12 and not matched&fresh and matched|fresh==set(range(1,464)) and fresh==set(read('eleventh-visual-review.json')['full_pages_reviewed']))
twelfth_rasters=read('twelfth-raster-comparison.json');cross=read('twelfth-cross-edition-review.json')
x=twelfth_rasters['pdfs'][-1]
matched={r['page'] for r in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies'])
current_reviewed={r['combined_page'] for r in cross['exact_matching_reviewed_bodies']}
outcomes['historical-twelfth-combined-raster-review-coverage']=(x['pdf_sha256']==prior_visual['pdf_sha256']==cross['combined_pdf_sha256'] and x['page_count']==479 and twelfth_rasters['crop_bottom_points']==cross['crop_bottom_points']==57 and twelfth_rasters['excluded_content_is_only_centered_footer_page_numbers'] and cross['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==457 and len(fresh)==22 and not matched&fresh and matched|fresh==set(range(1,480)) and len(current_reviewed)==20 and not current_reviewed&set(prior_visual['full_pages_reviewed']) and current_reviewed|set(prior_visual['full_pages_reviewed'])==fresh and cross['remaining_full_pages_to_review']==prior_visual['full_pages_reviewed'])

thirteenth_rasters=read('thirteenth-raster-comparison.json');cross13=read('thirteenth-cross-edition-review.json')
x=thirteenth_rasters['pdfs'][-1];matched={r['page'] for r in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);current_reviewed={r['combined_page'] for r in cross13['exact_matching_reviewed_bodies']}
visual13=read('thirteenth-visual-review.json')
outcomes['thirteenth-combined-raster-review-coverage']=(x['pdf_sha256']=='50c493eaf265a2d487f1fd1110e0d90682cb485840c88646e3280aa032c59ffa'==cross13['combined_pdf_sha256'] and x['page_count']==489 and thirteenth_rasters['crop_bottom_points']==cross13['crop_bottom_points']==57 and thirteenth_rasters['excluded_content_is_only_centered_footer_page_numbers'] and cross13['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==469 and len(fresh)==20 and not matched&fresh and matched|fresh==set(range(1,490)) and len(current_reviewed)==len(cross13['exact_matching_reviewed_bodies'])==14 and not current_reviewed&set(visual13['full_pages_reviewed']) and current_reviewed|set(visual13['full_pages_reviewed'])==fresh and cross13['remaining_full_pages_to_review']==visual13['full_pages_reviewed'])
x=read('weighted-arctangent-native.json')
outcomes['weighted-arctangent-native-exact-and-diagnostics']=x['all_pass'] and x['exact_passed'] and x['exact_checks']==7 and all(x['exact_results']) and x['working_precision']==70 and not x['interval_certified'] and x['numerical_checks']==17 and len(x['rows'])==17 and all(r['passed'] for r in x['rows'])
x=read('eleventh-replay/coincident/data/exact_validation.json')
outcomes['coincident-exact-engine']=x['status']=='passed' and x['moment_count']==420 and x['polynomial_count']==420 and x['total_checks']==1641
x=read('eleventh-replay/coincident/data/numerical_validation.json')
outcomes['coincident-independent-quadrature']=x['status']=='passed' and x['count']==49 and x['dps']==55 and all(r['passed'] for r in x['checks'])
x=read('eleventh-replay/dougall/results/exact_checks.json')
outcomes['centered-Dougall-exact']=x['status']=='PASS' and x['total_assertions']==485
x=read('eleventh-replay/dougall/results/numerical_checks.json')
outcomes['centered-Dougall-diagnostics']=x['status']=='PASS' and x['total_diagnostics']==293 and x['working_decimal_digits']==70 and all(Decimal(r['scaled_error'])<Decimal(r['tolerance']) for r in x['checks'])
x=read('eleventh-replay/identities/results/verification_summary.json')
outcomes['collision-and-weighted-full-suite']=x['status']=='all gates passed' and len(x['runs'])==7 and all(r['returncode']==0 for r in x['runs']) and x['numerical_comparisons']==167 and x['exact_nonlinear_checks']==213 and x['exact_collision_checks']==33 and x['exact_weighted_differential_checks']==4 and x['exact_weighted_coefficient_obstruction'] and not x['numerical_checks_are_certified_intervals']
x=read('eleventh-weighted-replay/weighted_arctangent_verification.json')
outcomes['weighted-delivery-full-suite']=x['numeric_check_count']==78 and Decimal(x['maximum_absolute_error'])<Decimal('1e-60') and x['exact_checks']['coefficient_discrepancy']=='1/36'
x=read('eleventh-weighted-replay/replay-summary.json')
outcomes['weighted-separate-replay-provenance']=x['passed'] and x['exit_code']==0 and digest(B.parent/'reports/stieltjes-correlation-calculus/continuations/collision-and-weighted-identities/code/verify_weighted_arctangent.py',False)==x['source_code_sha256'] and x['fresh_result_files']==['weighted_arctangent_verification.json']
x=read('eleventh-replay/jets/results/replay_summary.json')
outcomes['resonant-jets-full-six-script-suite']=x['all_passed'] and len(x['processes'])==6 and all(r['return_code']==0 for r in x['processes'])
x=read('eleventh-replay/triple/results/exact_checks.json')
outcomes['triple-Tornheim-exact']=x['status']=='PASS' and x['total_assertions']==621 and x['counts']['corruption_controls']==3
x=read('eleventh-replay/triple/results/numerical_checks.json')
outcomes['triple-Tornheim-independent-diagnostics']=x['status']=='PASS' and x['working_dps']==50 and x['total_comparisons']==56 and all(r['pass'] for r in x['comparisons'])
x=read('eleventh-replay/transport/results/nonlinear_checks.json')
outcomes['resonance-transport-nonlinear-exact']=x['status']=='passed' and x['exact_checks']==138 and x['independent_cutoff']['status']=='passed' and x['independent_cutoff']['case_count']==48 and x['independent_cutoff']['monomial_pairing_count']==140
x=read('eleventh-replay/transport/results/transport_checks.json')
outcomes['resonance-transport-diagnostics']=x['all_passed'] and x['exact_polynomial_checks']==4 and x['numeric_checks']==13 and not x['numerical_checks_are_interval_certificates']
x=read('eleventh-replay/transport/results/dougall_direct_checks.json')
outcomes['resonance-raw-harmonic-sums']=x['status']=='passed' and x['checkpoint_discrepancies_decrease'] and x['precision_digits']==50
# Twelfth intake: exact finite audits and diagnostic scopes remain distinct.
x=read('periodic-contact-table-comparison.json')
outcomes['periodic-contact-independent-tables']=(x['status']=='PASS' and x['left_table_formulas']==420 and x['right_table_formulas']==441 and x['common_exact_coefficients']==315 and x['corruption_controls']==2 and x['fixed_coordinate_base_contact']=='pi**2/3')
x=read('zeta-tail-identities.json')
outcomes['zeta-tail-finite-exact']=(x['status']=='PASS' and x['partial_fraction_orders']==list(range(2,33)) and x['sparse_coordinate_orders']==list(range(2,33)) and x['exact_bernoulli_checks']==2 and x['corruption_controls']==1)
d=x['numerical_diagnostics']
outcomes['zeta-tail-series-diagnostics']=(d['working_decimal_digits']==70 and d['head_terms']==120 and d['tail_orders']==[18,22] and not d['interval_certified'] and len(d['cases'])==10 and sum('tail_refinement' in r for r in d['cases'])==9 and all(r['passed'] and Decimal(r['absolute_residual'])<Decimal('1e-55') and Decimal(r.get('tail_refinement','0'))<Decimal('1e-55') for r in d['cases']))
x=read('periodic-contact-dougall-native.json')
outcomes['periodic-contact-Dougall-native-exact-and-Fourier']=(x['all_pass'] and x['exact_passed'] and x['exact_checks']==17 and all(x['exact_results']) and x['numerical_checks']==10 and len(x['rows'])==10 and all(r['passed'] for r in x['rows']) and x['working_precision']==60 and x['endpoint_phase_terms']==150 and x['phase_tail_bound_passed'] and not x['interval_certified'] and x['missing_atom_control']['rejected'])
x=read('dougall-gauss-native.json')
outcomes['Dougall-independent-double-Laplace-diagnostics']=(x['all_pass'] and x['working_precision']==65 and x['Gauss_orders']==[64,96] and x['outer_cutoff']==200 and len(x['rows'])==4 and all(r['passed'] for r in x['rows']) and not x['interval_certified'])
x=read('twelfth-replay/collisions/data/exact_checks.json')
outcomes['periodic-collision-finite-exact']=(x['status']=='all passed' and x['formula_count']==420 and x['exact_assertions']==760 and len(x['checks'])==760 and x['corruption_control_detected_missing_atom'])
x=read('twelfth-replay/collisions/data/numerical_checks.json')
outcomes['periodic-collision-Fourier-diagnostics']=(x['status']=='all passed' and x['working_decimal_precision']==60 and x['diagnostics']==40 and len(x['checks'])==40 and Decimal(x['maximum_scaled_error'])<Decimal('1e-40') and Decimal(x['missing_atom_control_error'])>3)
x=read('twelfth-replay/contact/data/exact_checks.json')
outcomes['periodic-contact-finite-exact']=(x['status']=='PASS' and x['check_count']==940 and len(x['checks'])==940 and x['contact_formula_count']==441)
x=read('twelfth-replay/contact/data/numerical_checks.json')
outcomes['periodic-contact-independent-diagnostics']=(x['status']=='PASS' and x['precision_dps']==55 and x['count']==69 and len(x['checks'])==69 and Decimal(x['maximum_relative_residual'])<Decimal('1e-40'))
x=read('twelfth-replay/directional/results/replay_summary.json')
outcomes['directional-full-ten-script-suite']=(x['all_passed'] and len(x['runs'])==10 and len(x['output_checks'])==9)
x=read('twelfth-replay/directional/results/contacts_verification.json')
outcomes['directional-independent-contacts']=(x['all_passed'] and x['precision_digits']==85 and x['argument_derivative_pairs']==21 and x['fourier_mode_checks']==189 and len(x['fourier_modes'])==189 and x['exact_reflection_checks']==21 and x['exact_displayed_coefficient_checks']==7 and x['numerical_reflection_checks']==63 and x['zero_mode_checks']==3 and Decimal(x['maximum_scaled_mode_residual'])<Decimal(x['configured_scaled_threshold']) and Decimal(x['missing_contact_negative_control_error'])>3)
x=read('twelfth-replay/directional/results/invariant_germs_verification.json')
outcomes['invariant-germs-finite-exact']=(x['all_passed'] and x['independent_residue_checks']==140 and x['stieltjes_threshold_checks']==440)
x=read('twelfth-replay/directional/results/s6_target_audit.json')
outcomes['S6-exact-target-audit-with-open-membership']=(x['result']=='PASS' and x['scale_after_exact_substitution']=='61/46080' and x['primitive_gcd']==1 and x['restricted_rows_annihilated']==192 and x['separator_original_target']==485683200 and x['separator_primitive_target']==642940 and x['exact_S6_depth3_reduction']=='S6=g61-g25+G*zeta5-beta7+Q7' and 'NOT a proof of S6' in x['scope'] and 'membership not computed' in x['remaining_exact_problem'])
x=read('twelfth-replay/directional/results/cubic_results.json')
outcomes['directional-cubic-Tornheim-diagnostic']=(x['precision_digits']==65 and Decimal(x['cubic_residual'])<Decimal('1e-28') and Decimal(x['T1_residual'])<Decimal('1e-35') and Decimal(x['T2_residual'])<Decimal('1e-35'))
x=read('twelfth-replay/mixed/results/replay_summary.json')
outcomes['mixed-spectral-full-four-script-suite']=x['all_scripts_completed'] and len(x['runs'])==4
x=read('twelfth-replay/mixed/results/harmonic.json')
outcomes['mixed-harmonic-Newton-diagnostics']=(x['all_thresholds_passed'] and x['working_precision_decimal_digits']==180 and x['newton_terms']==240 and len(x['checks'])==26)
x=read('twelfth-replay/mixed/results/dougall.json')
outcomes['mixed-Dougall-Bell-and-diagnostics']=(x['all_thresholds_passed'] and x['decimal_precision']==65 and len(x['numerical'])==13 and len(x['exact_bell'])==6 and len(x['exact_grid_polynomials'])==21)
x=read('twelfth-replay/mixed/results/twists.json')
outcomes['mixed-unequal-twists-replay']=(x['status']=='passed' and x['working_decimal_digits']==65 and x['exact_assertions']==51 and len(x['exact_checks'])==51 and x['numerical_comparisons']==18 and len(x['numerical_checks'])==18)
x=read('twelfth-replay/ordered/results/ordered_core_exact_checks.json')
outcomes['ordered-Hurwitz-finite-exact']=x['number_of_checks']==60 and len(x['checks'])==60 and x['status']=='all exact formal checks passed'
x=read('twelfth-replay/ordered/results/ordered_audit.json');y=read('twelfth-replay/ordered/results/cubic_audit.json')
outcomes['ordered-and-cubic-symbolic-audit']=x['passed']==len(x['checks'])==7 and y['passed']==len(y['checks'])==5
x=read('twelfth-replay/ordered/results/ordered_numeric_50dps.json')
outcomes['ordered-Hurwitz-Laurent-diagnostics']=(x['diagnostic_passed'] and x['precision_dps']==50 and x['cauchy_points']==20 and x['cutoff']==36 and x['em_order']==20 and len(x['checks'])==7 and Decimal(x['maximum_comparison_residual'])<Decimal(x['diagnostic_tolerance']))
x=read('twelfth-replay/ordered/results/cubic_validation_35dps.json')
outcomes['ordered-independent-cubic-diagnostic']=(x['diagnostic_passed'] and x['dps']==35 and x['jonquiere_terms']==50 and Decimal(x['absolute_residual'])<Decimal(x['diagnostic_tolerance']))
# Thirteenth intake: selected accepted cores; other deliveries remain pending.
x=read('thirteenth-incoming-retirement.json')
outcomes['thirteenth-archive-retirement']=(x['archive_count']==18 and x['preserved_members']==649 and x['original_members']==661 and x['archive_only_members']==12 and len(x['archives'])==18 and all(a['retired'] and not (B.parents[3]/a['archive']).exists() and a['arrival_commit']==archive_by_path[a['archive']]['archive_git_revision'] and a['members']==len(archive_by_path[a['archive']]['files']) for a in x['archives']))
for part in ['exact-resonant','parity']:
    x=read(f'thirteenth-replay/{part}/replay-summary.json');folder=B.parent/'reports'/x['source_folder']
    outcomes['thirteenth-selected-replay/'+part]=(x['passed'] and len(x['commands'])==1 and all(c['exit_code']==0 for c in x['commands']) and bool(x['fresh_result_files']) and all((V/'thirteenth-replay'/part/p).is_file() for p in x['fresh_result_files']) and all(digest(folder/p,False)==h for p,h in x['source_code_sha256'].items()))
x=read('thirteenth-replay/exact-resonant/complete-cayley-verification.json')
outcomes['full-Cayley-ideal-exact-certificate']=(x['result']=='PASS' and x['ambient_adapted_odd_dimension']==2546 and x['functional_support']==2476 and x['inherited_rows_regenerated']==5131 and x['row_counts']=={'DS':3460,'DIST':1394,'LIFT':40,'CAYLEY_BALANCED_LIFT':237} and x['complete_cayley_basis_checks']==2546 and x['nonzero_projector_difference_rows']==2300 and x['target_normalization']==128588 and x['target_pairing']==-186660627289236812620583691130496682078843750753489297279472069700354208 and x['projector_audits']=={'words_through_weight_four':780,'shuffle_products_through_weight_four':2150,'independent_consecutive_cut_eulerian_checks':780} and 'remains conjectural' in x['period_status'])
x=read('full-cayley-target-normalization.json')
outcomes['full-Cayley-printed-target-independent-audit']=(x['status']=='PASS' and x['printed_target_coefficients_checked']==7 and x['target_normalization']==128588 and x['exact_pairing']==-int(x['positive_integer_decomposition']) and x['corruption_controls']==1)
x=read('centered-trigamma-native.json')
outcomes['centered-trigamma-native-exact-and-diagnostics']=(x['all_pass'] and x['exact_passed'] and x['exact_checks']==29 and all(x['exact_results']) and x['corruption_controls']==1 and x['corruption_detected'] and x['working_precision']==85 and x['series_heads']==[120,160] and x['asymptotic_tail_orders']==[24,30] and x['numerical_checks']==len(x['rows'])==7 and all(r['passed'] for r in x['rows']) and not x['interval_certified'])
x=read('thirteenth-replay/parity/results/latest/run_summary.json')
outcomes['harmonic-parity-full-five-script-suite']=(x['status']=='passed' and x['mode']=='full' and len(x['jobs'])==5 and all(r['returncode']==0 for r in x['jobs']))
x=read('thirteenth-replay/parity/results/latest/harmonic_parity_checks.json')
outcomes['centered-moment-independent-series-and-generator']=(x['status']=='all checks passed' and x['precision_digits']==110 and len(x['exact_parity'])==8 and len(x['finite_sum_constants'])==8 and x['formal_trigamma_shift_equation_to_order']==14 and len(x['general_shift_T_r_checks'])==2 and set(x['centered_trigamma_square_values'])==set(map(str,range(7))) and len(x['polylog_generator'])==3 and all(Decimal(r['absolute_error'])<Decimal('1e-70') and Decimal(r['two_cutoff_difference'])<Decimal('1e-65') for r in x['centered_trigamma_square_values'].values()) and all(Decimal(r['closed_vs_moment_series_error'])<Decimal('1e-85') and Decimal(r['closed_vs_integral_error'])<Decimal('1e-95') for r in x['polylog_generator'].values()))
x=read('thirteenth-replay/parity/results/latest/resolvent_checks.json')
outcomes['full-resolvent-direct-Stieltjes-and-complex-order-diagnostics']=(x['full'] and x['exact_assertions']==55 and x['working_precision_digits']==55 and x['numerical_checks']==len(x['checks'])==28 and all(Decimal(r['absolute_error'])<Decimal(r['tolerance']) for r in x['checks']))
x=read('thirteenth-replay/parity/results/latest/resolvent_contact_checks.json')
outcomes['completed-resolvent-independent-contact-diagnostics']=(x['status']=='all checks passed' and x['digits']==100 and bool(x['checks']))
volume_build=read('volume-build-results.json')
volume_inspection=read('volume-inspection.json')
volume_visual=read('volume-visual-review.json')
volume_standalone=read('volume-standalone-results.json')
volume_plan=read('volume-plan.json')
outcomes['four-volume-build']=volume_build['passed'] and volume_build['converged'] and len(volume_build['volumes'])==4 and len(volume_build['rounds'])>=3 and volume_build['rounds'][-1]['reference_state_sha256']==volume_build['rounds'][-2]['reference_state_sha256']
outcomes['four-volume-partition-and-links']=volume_inspection['passed'] and volume_inspection['chapter_partition_complete'] and volume_inspection['total_pages']==669 and volume_inspection['external_destinations_verified']==70 and not volume_inspection['issues']
outcomes['four-volume-independent-compilation']=volume_standalone['passed'] and len(volume_standalone['volumes'])==4 and all(x['passed'] and x['text_matches_primary'] and x['PDF_link_targets_match'] and len(x['passes'])==3 for x in volume_standalone['volumes'])
outcomes['four-volume-recorded-visual-review']=(volume_visual['passed'] and not volume_visual['findings'] and volume_visual['total_pages']==669 and volume_visual['total_contact_sheets_reviewed']==0 and volume_visual['total_contact_sheets_covered']==44 and len(volume_visual['volumes'])==4)
prior_volume_visual=read('twelfth-volume-visual-review.json')
raster_comparison=read('eleventh-volume-raster-comparison.json')
outcomes['historical-weighted-volume-raster-review-coverage']=(sum(len(x['same_index_identical_pages']) for x in raster_comparison['volumes'][1:])==367 and all(not set(x['same_index_identical_pages'])&set(x['changed_pages']) and set(x['same_index_identical_pages'])|set(x['changed_pages'])==set(range(1,x['page_count']+1)) and x['pdf_sha256']==next(r for r in twelfth_rasters['pdfs'] if r['pdf']==x['pdf'])['previous_pdf_sha256'] for x in raster_comparison['volumes']))
outcomes['historical-twelfth-volume-raster-review-coverage']=(sum(len(x['same_index_full_raster_matches']) for i,x in enumerate(twelfth_rasters['pdfs'][:4]) if i!=2)==327 and all(not {r['page'] for r in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {r['page'] for r in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and next(r for r in thirteenth_rasters['pdfs'] if r['pdf']==x['pdf'])['previous_pdf_sha256']==x['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(prior_volume_visual['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(twelfth_rasters['pdfs'][:4])) and prior_volume_visual['volumes'][2]['fresh_contact_sheets_reviewed']==12 and cross['volume_3_pdf_sha256']==prior_volume_visual['volumes'][2]['pdf_sha256'] and all(r['reviewed_volume_3_page'] in prior_volume_visual['volumes'][2]['full_pages_reviewed'] for r in cross['exact_matching_reviewed_bodies']))

visual_vol13=read('thirteenth-volume-visual-review.json')
outcomes['thirteenth-volume-raster-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in thirteenth_rasters['pdfs'][:4])==499 and sum(len(x['changed_scientific_bodies']) for x in thirteenth_rasters['pdfs'][:4])==28 and all(not {r['page'] for r in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {r['page'] for r in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and visual_vol13['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(visual_vol13['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(thirteenth_rasters['pdfs'][:4])) and all(r['reviewed_volume_page'] in visual_vol13['volumes'][r['volume_number']-1]['full_pages_reviewed'] and r['pdf_sha256']==visual_vol13['volumes'][r['volume_number']-1]['pdf_sha256'] for r in cross13['exact_matching_reviewed_bodies']))
for number,pages in [(1, 190), (2, 131), (3, 261), (4, 87)]:
    item=next(x for x in volume_build['volumes'] if x['number']==number)
    inspection=next(x for x in volume_inspection['volumes'] if x['number']==number)
    review=next(x for x in volume_visual['volumes'] if x['number']==number)
    plan=next(x for x in volume_plan if x['number']==number)
    driver=(B/item['source']).read_text(encoding='utf-8')
    assignments=[(int(n)+1,name) for n,name in re.findall(r'\\setcounter\{chapter\}\{(\d+)\}\s*\\input\{chapters/([^}]+)\}',driver)]
    outcomes[f'volume-{number}-artifact-agreement']=(digest(B/item['pdf'],False)==item['pdf_sha256']==inspection['pdf_sha256']==review['pdf_sha256'] and inspection['page_count']==review['page_count']==pages and inspection['pdf_author']=='ProveIt Contributors' and assignments==[tuple(x) for x in plan['chapters']])

fourteenth_rasters=read('fourteenth-raster-comparison.json');cross14=read('fourteenth-cross-edition-review.json')
x=fourteenth_rasters['pdfs'][-1];matched={r['page'] for r in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={r['combined_page'] for r in cross14['exact_matching_reviewed_bodies']}
visual14=read('fourteenth-visual-review.json')
outcomes['fourteenth-combined-review-coverage']=(x['pdf_sha256']=='5432bc34cdc98558d2f7b4e480e1b54e60d4e397935f9ab6e54eb962061220b2'==cross14['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual13['pdf_sha256'] and x['page_count']==507 and fourteenth_rasters['crop_bottom_points']==cross14['crop_bottom_points']==57 and fourteenth_rasters['excluded_content_is_only_centered_footer_page_numbers'] and cross14['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==484 and len(fresh)==23 and not matched&fresh and matched|fresh==set(range(1,508)) and len(reviewed)==18 and not reviewed&set(visual14['full_pages_reviewed']) and reviewed|set(visual14['full_pages_reviewed'])==fresh and cross14['remaining_full_pages_to_review']==visual14['full_pages_reviewed'])
visual_vol14=read('fourteenth-volume-visual-review.json')
outcomes['fourteenth-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in fourteenth_rasters['pdfs'][:4])==518 and sum(len(x['changed_scientific_bodies']) for x in fourteenth_rasters['pdfs'][:4])==27 and all(not {r['page'] for r in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {r['page'] for r in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and visual_vol14['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==visual_vol13['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(visual_vol14['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(fourteenth_rasters['pdfs'][:4])) and all(r['reviewed_volume_page'] in visual_vol14['volumes'][r['volume_number']-1]['full_pages_reviewed'] and r['pdf_sha256']==visual_vol14['volumes'][r['volume_number']-1]['pdf_sha256'] for r in cross14['exact_matching_reviewed_bodies']))
x=read('fourteenth-incoming-retirement.json')
outcomes['fourteenth-archive-retirement']=(x['archive_count']==6 and x['preserved_members']==189 and x['original_members']==194 and x['archive_only_members']==5 and len(x['archives'])==6 and all(a['retired'] and not (B.parents[3]/a['archive']).exists() and a['arrival_commit']==archive_by_path[a['archive']]['archive_git_revision'] and a['members']==len(archive_by_path[a['archive']]['files']) for a in x['archives']))
for part,count in [('gauss',1),('canonical',1),('continuous',2),('powers',3),('mixed',1),('tilted',3)]:
    x=read(f'fourteenth-replay/{part}/replay-summary.json');folder=B.parent/'reports'/x['source_folder']
    outcomes['fourteenth-full-mathematical-replay/'+part]=(x['passed'] and len(x['commands'])==count and all(c['exit_code']==0 for c in x['commands']) and bool(x['fresh_result_files']) and all((V/'fourteenth-replay'/part/p).is_file() for p in x['fresh_result_files']) and all(digest(folder/p,False)==h for p,h in x['source_code_sha256'].items()))
x=read('digamma-powers-native.json')
outcomes['digamma-powers-native-exact-and-diagnostics']=(x['all_pass'] and x['all_exact_passed'] and x['exact_closed_residue_polynomials']==10 and all(x['exact_results']) and x['working_precision']==100 and x['local_taylor_degree']==130 and x['local_split']=='1/10' and x['checked_moment_diagnostics']==3 and x['corruption_controls']==1 and x['corruption_detected'] and not x['interval_certified'])
x=read('digamma-coordinate-source-audit.json');sign=x['gamma1_sign_certificate']
outcomes['digamma-fifth-coordinate-and-polynomial-audit']=(x['status']=='PASS' and x['fifth_coordinate_identity'] and x['missing_stieltjes_control']=='20*gamma1*z3' and x['fifth_polynomial_cancellations']==4 and x['canonical_fifth_scalar_verified'] and x['regular_pole_polynomial_difference_verified'])
outcomes['positive-Cauchy-finite-coefficient-audit']=(x['positive_Cauchy_coefficients_checked']==16 and x['independent_binomial_and_log_series_equalities']==32)
outcomes['primary-source-Stieltjes-counterexamples']=(sign['N']==10 and sign['atanh_terms']==128 and Fraction(-3,40)<Fraction(sign['exact_lower'])<=Fraction(sign['exact_upper'])<Fraction(-7,100) and x['source_index_counterexample']=={'m':0,'a':1,'printed_limit_minus_correct_limit':-1})
x=read('S6-depth-five-escape-probe.json')
outcomes['S6-selected-exact-depth-five-escapes']=(x['status']=='PASS' and x['tested_inputs']==22 and x['bounded_projected_rows']==22 and x['bounded_nonzero_pairings']==19 and len(x['rows'])==22 and all('projected_relation' in r for r in x['rows']))
x=read('S6-depth-five-bounded-intersection.json')
outcomes['S6-exact-depth-five-cancellation']=(x['status']=='PASS' and x['input_rows']==190 and x['top_sector_exact_rank']==166 and x['kernel_dimension']==24 and x['nonzero_distinct_bounded_relations']==24 and len(x['bounded_relations'])==24 and digest(V/'S6-depth-five-extended-probe.json',False)==x['source_probe_sha256'])
x=read('S6-intersection-native-search.json');m=read('S6-intersection-integer-matrix.json')
outcomes['S6-enlarged-modular-search-integrity']=(x['status']=='SEARCH_DIAGNOSTIC' and x['prime']==2147483647 and x['rows']==m['rows']==5155 and x['columns']==m['columns']==2546 and x['common_denominator']==m['common_denominator']==384 and x['rank']==1897 and not x['target_modular_member'] and x['matrix_sha256']==m['matrix_sha256'] and digest(V/'s6_modular_solver.cpp',True)==x['source_cpp_sha256'] and digest(V/'S6-depth-five-bounded-intersection.json',False)==m['probe_sha256'])


fifteenth_rasters=read('fifteenth-raster-comparison.json');cross15=read('fifteenth-cross-edition-review.json')
x=fifteenth_rasters['pdfs'][-1];matched={r['page'] for r in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={r['combined_page'] for r in cross15['exact_matching_reviewed_bodies']}
visual15=read('fifteenth-visual-review.json')
outcomes['fifteenth-combined-review-coverage']=(x['pdf_sha256']=='a6da216137e7c9ad78deb27957b91d8ac11cec660174a9575006cd4cd62398dd'==cross15['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual14['pdf_sha256'] and x['page_count']==510 and fifteenth_rasters['crop_bottom_points']==cross15['crop_bottom_points']==57 and fifteenth_rasters['excluded_content_is_only_centered_footer_page_numbers'] and cross15['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==502 and len(fresh)==8 and not matched&fresh and matched|fresh==set(range(1,511)) and len(reviewed)==6 and not reviewed&set(visual15['full_pages_reviewed']) and reviewed|set(visual15['full_pages_reviewed'])==fresh and cross15['remaining_full_pages_to_review']==visual15['full_pages_reviewed'])
visual_vol15=read('fifteenth-volume-visual-review.json')
outcomes['fifteenth-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in fifteenth_rasters['pdfs'][:4])==538 and sum(len(x['changed_scientific_bodies']) for x in fifteenth_rasters['pdfs'][:4])==10 and all(not {r['page'] for r in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {r['page'] for r in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and visual_vol15['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==visual_vol14['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(visual_vol15['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(fifteenth_rasters['pdfs'][:4])) and all(r['reviewed_volume_page'] in visual_vol15['volumes'][r['volume_number']-1]['full_pages_reviewed'] and r['pdf_sha256']==visual_vol15['volumes'][r['volume_number']-1]['pdf_sha256'] for r in cross15['exact_matching_reviewed_bodies']))
x=read('fifteenth-incoming-retirement.json')
outcomes['fifteenth-archive-retirement']=(x['archive_count']==6 and x['preserved_members']==217 and x['original_members']==220 and x['archive_only_members']==3 and len(x['archives'])==6 and all(a['retired'] and not (B.parents[3]/a['archive']).exists() and a['arrival_commit']==archive_by_path[a['archive']]['archive_git_revision'] and a['members']==len(archive_by_path[a['archive']]['files']) for a in x['archives']))
for part,count in [('bernoulli',1),('cubic',2),('determinantal',2),('differential',1),('multishift',3),('tails',1)]:
    x=read(f'fifteenth-replay/{part}/replay-summary.json');folder=B.parent/'reports'/x['source_folder']
    outcomes['fifteenth-full-mathematical-replay/'+part]=(x['passed'] and len(x['commands'])==count and all(c['exit_code']==0 for c in x['commands']) and bool(x['fresh_result_files']) and all((V/'fifteenth-replay'/part/p).is_file() for p in x['fresh_result_files']) and all(digest(folder/p,False)==h for p,h in x['source_code_sha256'].items()))
x=read('differential-polynomials-native.json')
outcomes['derivative-ideal-independent-native-replay']=(x['all_pass'] and x['frozen_residue_checks']==16 and x['all_exact_passed'] and all(x['exact_results']) and x['scalar_negative_control_detected'] and x['working_precision']==90 and x['local_taylor_degree']==105 and x['local_split']=='1/10' and len(x['moment_diagnostics'])==3 and all(r['passed'] for r in x['moment_diagnostics']) and not x['interval_certified'])
x=read('fifteenth-replay/differential/verification/conjecture_audit/differential_exact_results.json')
outcomes['derivative-ideal-independent-finite-audit']=(not x['imports_article_or_incoming_code'] and not x['numerical_period_recognition'] and x['residue_filter']['maximum_weight']==10 and x['residue_filter']['mixed_laurent_residues_checked']==128 and x['residue_filter']['scalar_laurent_residues_checked']==10 and x['bilinear']['pairs_checked']==48 and x['bilinear']['direct_pole_identities_checked']==96)
x=read('fifteenth-replay/differential/results/differential_numeric.json')
outcomes['differential-calculus-independent-diagnostics']=(x['status']=='passed' and x['working_decimal_digits']==90 and x['taylor_order']==160 and x['assertions']==40 and Decimal(x['maximum_relative_residual'])<Decimal('1e-80'))


ibp_rasters=read('ibp-raster-comparison.json');cross_ibp=read('ibp-cross-edition-review.json')
x=ibp_rasters['pdfs'][-1];matched={r['page'] for r in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={r['combined_page'] for r in cross_ibp['exact_matching_reviewed_bodies']}
visual_ibp=read('ibp-visual-review.json')
outcomes['ibp-combined-review-coverage']=(x['pdf_sha256']=='bdec50ddc82561d7ba483a46c215f17219e257fcec68f480f49abd30832eb2d5'==cross_ibp['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual15['pdf_sha256'] and x['page_count']==513 and ibp_rasters['crop_bottom_points']==cross_ibp['crop_bottom_points']==57 and ibp_rasters['excluded_content_is_only_centered_footer_page_numbers'] and cross_ibp['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==506 and len(fresh)==7 and not matched&fresh and matched|fresh==set(range(1,514)) and len(reviewed)==5 and not reviewed&set(visual_ibp['full_pages_reviewed']) and reviewed|set(visual_ibp['full_pages_reviewed'])==fresh and cross_ibp['remaining_full_pages_to_review']==visual_ibp['full_pages_reviewed'])
visual_vol_ibp=read('ibp-volume-visual-review.json')
outcomes['ibp-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in ibp_rasters['pdfs'][:4])==545 and sum(len(x['changed_scientific_bodies']) for x in ibp_rasters['pdfs'][:4])==6 and all(not {r['page'] for r in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {r['page'] for r in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and visual_vol_ibp['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==visual_vol15['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(visual_vol_ibp['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(ibp_rasters['pdfs'][:4])) and all(r['reviewed_volume_page'] in visual_vol_ibp['volumes'][r['volume_number']-1]['full_pages_reviewed'] and r['pdf_sha256']==visual_vol_ibp['volumes'][r['volume_number']-1]['pdf_sha256'] for r in cross_ibp['exact_matching_reviewed_bodies']))
x=read('ibp-normal-forms-exact.json')
outcomes['ibp-independent-rational-matrices-and-Gamma-parity']=(x['status']=='PASS' and x['matrix_weights']==[2,14] and len(x['matrices'])==13 and all(r['both_inverse_certificates'] and r['factor_degree_preserved'] for r in x['matrices']) and x['monomial_decompositions_checked']==sum(r['ambient_dimension'] for r in x['matrices'])==506 and x['inverse_gamma_degrees']==[2,12] and x['factor_parity_checks']==x['independent_Bell_generator_checks']==x['independent_Lagrange_concomitant_checks']==x['pair_recurrence_checks']==11 and x['printed_normal_forms_checked']==5 and x['endpoint_checks']==3 and x['missing_cross_pole_control_detected'])
x=read('ibp-endpoints-native.json')
outcomes['ibp-independent-native-endpoints-and-identities']=(x['all_pass'] and x['exact_endpoint_checks']==3 and x['all_exact_passed'] and all(x['exact_results']) and x['missing_endpoint_control_detected'] and x['working_precision']==90 and x['local_taylor_degree']==105 and x['local_split']=='1/10' and len(x['moment_diagnostics'])==2 and all(r['passed'] for r in x['moment_diagnostics']) and not x['interval_certified'])


visual_appell=read('appell-visual-review.json');visual_vol_appell=read('appell-volume-visual-review.json')
appell_rasters=read('appell-raster-comparison.json');cross_appell=read('appell-cross-edition-review.json')
x=appell_rasters['pdfs'][-1];matched={r['page'] for r in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={r['combined_page'] for r in cross_appell['exact_matching_reviewed_bodies']}
outcomes['appell-combined-review-coverage']=(x['pdf_sha256']==visual_appell['pdf_sha256']==cross_appell['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_ibp['pdf_sha256'] and x['page_count']==517 and appell_rasters['crop_bottom_points']==cross_appell['crop_bottom_points']==57 and appell_rasters['excluded_content_is_only_centered_footer_page_numbers'] and cross_appell['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==511 and len(fresh)==6 and not matched&fresh and matched|fresh==set(range(1,518)) and len(reviewed)==4 and not reviewed&set(visual_appell['full_pages_reviewed']) and reviewed|set(visual_appell['full_pages_reviewed'])==fresh and cross_appell['remaining_full_pages_to_review']==visual_appell['full_pages_reviewed'])
outcomes['appell-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in appell_rasters['pdfs'][:4])==550 and sum(len(x['changed_scientific_bodies']) for x in appell_rasters['pdfs'][:4])==5 and all(not {r['page'] for r in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {r['page'] for r in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and visual_vol_appell['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==visual_vol_ibp['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(visual_vol_appell['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(appell_rasters['pdfs'][:4])) and all(r['reviewed_volume_page'] in visual_vol_appell['volumes'][r['volume_number']-1]['full_pages_reviewed'] and r['pdf_sha256']==visual_vol_appell['volumes'][r['volume_number']-1]['pdf_sha256'] for r in cross_appell['exact_matching_reviewed_bodies']))
x=read('appell-tail-normalization-exact.json')
outcomes['appell-independent-tail-and-coordinate-audit']=(x['status']=='PASS' and x['degrees']==[2,9] and len(x['records'])==8 and all(r['tail_ideal'] and r['degree_bound'] and r['finite_difference_convergence_rule'] for r in x['records']) and x['lower_moment_coordinate_checks']==[2,3,4,5] and x['formal_transport_checks']==7 and x['missing_Stieltjes_control_detected'])
x=read('appell-cauchy-native.json')
outcomes['appell-independent-native-Cauchy-comparison']=(x['all_pass'] and x['even_zeta_normalization_checks']==1 and x['all_exact_passed'] and all(x['exact_results']) and x['working_precision']==110 and x['Cauchy_Mellin_cutoff']==160 and x['local_taylor_degree']==105 and x['local_split']=='1/10' and len(x['moment_diagnostics'])==3 and all(r['passed'] for r in x['moment_diagnostics']) and not x['interval_certified'])


# Sixteenth intake and accepted sixth/seventh scalar reductions.
x=read('sixteenth-incoming-retirement.json')
outcomes['sixteenth-archive-retirement']=(x['archive_count']==6 and x['preserved_members']==174 and x['original_members']==177 and x['archive_only_members']==3 and len(x['archives'])==6 and all(a['retired'] and not (B.parents[3]/a['archive']).exists() and a['arrival_commit']==archive_by_path[a['archive']]['archive_git_revision'] and a['members']==len(archive_by_path[a['archive']]['files']) for a in x['archives']))
for part,count in [('beta',2),('gamma',1),('shifts',3),('reconstruction',1),('quadratic',2),('same-direction',2)]:
    x=read(f'sixteenth-replay/{part}/replay-summary.json');folder=B.parent/'reports'/x['source_folder']
    outcomes['sixteenth-full-mathematical-replay/'+part]=(x['passed'] and len(x['commands'])==count and all(c['exit_code']==0 for c in x['commands']) and bool(x['fresh_result_files']) and all((V/'sixteenth-replay'/part/p).is_file() for p in x['fresh_result_files']) and all(digest(folder/p,False)==h for p,h in x['source_code_sha256'].items()))
x=read('appell-six-seven-exact.json')
outcomes['sixth-seventh-ordinary-exact-certificates']=(x['status']=='PASS' and [(r['weight'],r['rows'],r['rank']) for r in x['ordinary_certificates']]==[(5,21,8),(6,49,16)] and all(r['both_inverse_products'] and r['all_row_residuals_zero'] and r['corruption_rejected'] for r in x['ordinary_certificates']) and x['supplied_weight_six_rows_regenerated']==49)
outcomes['sixth-seventh-marked-exact-certificates']=(len(x['moments'])==2 and [(r['degree'],len(r['Dwords'])) for r in x['moments']]==[(6,13),(7,32)] and all(r['printed_directional_formula_verified'] and r['derivative_corruption_rejected'] for r in x['moments']) and [r['J_reduced'] for r in x['moments']]==['245*z2*z3 + 175*z5','3731*z3**2/4 + 918631*z6/240'])
x=read('appell-six-seven-native.json')
outcomes['sixth-seventh-independent-native-diagnostics']=(x['all_pass'] and x['working_precision']==110 and x['local_taylor_degree']==105 and x['local_split']=='1/10' and x['Cauchy_Mellin_cutoff']==200 and x['head_and_tail_configurations']==[[96,42],[128,48]] and len(x['moments'])==2 and all(r['passed'] for r in x['moments']) and not x['interval_certified'])
x=read('S6-full-depth-five-probe-summary.json')
outcomes['S6-complete-single-X-input-record']=(x['status']=='PASS' and x['tested_inputs']==1032 and x['bounded_projected_rows']==22 and x['bounded_nonzero_pairings']==19 and digest(V/'S6-full-depth-five-probe.json.gz',False)==x['compressed_records_sha256'])
x=read('S6-full-depth-five-kernel-certificate.json')
outcomes['S6-complete-single-X-exact-kernel']=(x['status']=='PASS' and x['input_rows']==1032 and x['top_columns']==6240 and x['exact_top_rank']==1008 and x['exact_kernel_dimension']==24 and x['old_rows_matched']==190 and x['exact_bounded_reconstructions']==24 and len(set(x['independent_kernel_leading_indices']))==24 and len(x['minor_row_indices'])==len(x['minor_column_indices'])==1008 and x['prime']==2147483647 and x['minor_determinant_mod_prime']==221991308 and digest(V/'S6-full-depth-five-probe.json.gz',False)==x['compressed_probe_sha256'])
x=read('S6-full-depth-five-matrix.json');y=read('S6-full-depth-five-native-search.json')
outcomes['S6-full-input-modular-search-scope']=(x['rows']==y['rows']==6187 and x['columns']==y['columns']==8786 and x['common_denominator']==y['common_denominator']==5760 and x['maximum_absolute_integer']==4704007680 and x['maximum_includes_target'] and y['status']=='SEARCH_DIAGNOSTIC' and y['rank']==2905 and not y['target_modular_member'] and y['matrix_sha256']==x['matrix_sha256'] and digest(V/'s6_modular_solver.cpp',True)==y['source_cpp_sha256'])
visual_higher=read('higher-appell-visual-review.json');volume_higher=read('higher-appell-volume-visual-review.json')
r=read('higher-appell-raster-comparison.json');c=read('higher-appell-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['higher-appell-combined-review-coverage']=(x['pdf_sha256']==visual_higher['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_appell['pdf_sha256'] and x['page_count']==521 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==511 and len(fresh)==10 and not matched&fresh and matched|fresh==set(range(1,522)) and len(reviewed)==8 and not reviewed&set(visual_higher['full_pages_reviewed']) and reviewed|set(visual_higher['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_higher['full_pages_reviewed'])
outcomes['higher-appell-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==549 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==10 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_higher['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==visual_vol_appell['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_higher['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_higher['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_higher['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


for family,count,bounded,escapes in [('Y',1144,0,0),('H',1032,0,0),('B',1032,22,19)]:
    x=read(f'S6-{family}-depth-five-probe-summary.json')
    outcomes['S6-complete-first-letter-input/'+family]=(x['status']=='PASS' and x['tested_inputs']==count and x['bounded_projected_rows']==bounded and x['bounded_nonzero_pairings']==escapes and digest(V/f'S6-{family}-depth-five-probe.json.gz',False)==x['compressed_records_sha256'])
x=read('S6-all-letters-depth-five-matrix.json');y=read('S6-all-letters-depth-five-native-search.json')
outcomes['S6-all-first-letter-modular-search-scope']=(x['rows']==y['rows']==9395 and x['new_full_first_letter_rows']==4240 and x['columns']==y['columns']==8786 and x['common_denominator']==y['common_denominator']==5760 and x['maximum_absolute_integer']==4704007680 and x['maximum_includes_target'] and y['status']=='SEARCH_DIAGNOSTIC' and y['rank']==4942 and not y['target_modular_member'] and y['matrix_sha256']==x['matrix_sha256'] and y['source_probe_sha256']==x['source_probe_sha256'] and digest(V/'s6_modular_solver.cpp',True)==y['source_cpp_sha256'] and all(x['source_probe_sha256'][family]==read('S6-'+('full' if family=='full' else family)+'-depth-five-probe-summary.json')['compressed_records_sha256'] for family in ['full','Y','H','B']))


# Accepted beta-crossing and ordinary logarithmic-moment cores.
x=read('beta-crossing-independent.json');d=x['numerical_diagnostics']
outcomes['beta-crossing-independent-exact-core']=(x['status']=='PASS' and not x['imports_delivered_code'] and len(x['affine_density_polynomials'])==12 and all(r['passed'] for r in x['affine_density_polynomials']) and len(x['balanced_jet_checks'])==26 and all(r['passed'] for r in x['balanced_jet_checks']) and len(x['chamber_rank_checks'])==378 and all(r['rank']==r['occupied_chambers']-1 and r['balanced_kernel_dimension']==r['factors']-r['occupied_chambers'] for r in x['chamber_rank_checks']) and all(x['corruption_controls'].values()))
outcomes['beta-centered-logarithms-independent-exact-reduction']=(len(x['ordinary_moment_coefficient_checks'])==128 and all(r['passed'] and r['logarithmic_order']>=r['r']+r['s'] for r in x['ordinary_moment_coefficient_checks']))
outcomes['beta-crossing-independent-numerical-diagnostics']=(d['working_digits']==90 and d['local_taylor_orders']==[80,90] and d['local_radius_fraction']=='1/4' and not d['interval_certified'] and len(d['scalar_cases'])==12 and all(r['passed'] and all(Decimal(r[k])<Decimal('1e-30') for k in ['finite_part_error','local_refinement','density_derivative_error']) for r in d['scalar_cases']) and len(d['principal_log_phase_cases'])==33 and all(r['passed'] and Decimal(r['error'])<Decimal('1e-80') for r in d['principal_log_phase_cases']) and len(d['ordinary_mellin_cases'])==9 and all(r['passed'] and Decimal(r['absolute_error'])<Decimal('1e-75') for r in d['ordinary_mellin_cases']))
for length,entries,bounded,den in [(2,18672239,14,2880),(3,20962269,2,5760)]:
    stem=f'S6-split-{length}-{7-length}-depth-five';x=read(stem+'-packing.json')
    outcomes['S6-lossless-convergent-input-packing/'+str(length)]=(x['status']=='PASS' and x['length_split']==[length,7-length] and x['rows']==3604 and x['columns']==8786 and x['common_denominator']==5760 and x['source_projected_denominator']==den and x['entries']==entries and x['bounded_rows']==bounded and digest(V/(stem+'-sparse.bin.gz'),False)==x['compact_sha256'])
x=read('S6-convergent-split-input-audit.json')
outcomes['S6-independent-convergent-input-covers']=(x['status']=='PASS' and not x['imports_delivered_code'] and x['depth_five_odd_coefficient']==3604 and len(x['families'])==2 and sum(r['entries'] for r in x['families'])==39634508 and all(r['input_cover_complete'] and r['rows']==3604 and r['missing_input_control_rejected'] and r['compact_sha256']==read('S6-split-'+str(r['length_split'][0])+'-'+str(r['length_split'][1])+'-depth-five-packing.json')['compact_sha256'] for r in x['families']))
x=read('S6-convergent-splits-matrix.json')
outcomes['S6-complete-convergent-integer-input-integrity']=(x['status']=='PASS' and x['rows']==16603 and x['columns']==8786 and x['previous_rows']==9395 and x['new_convergent_rows']==7208 and x['common_denominator']==5760 and x['maximum_absolute_integer']==4704007680 and x['maximum_includes_target'] and x['previous_matrix_sha256']==read('S6-all-letters-depth-five-matrix.json')['matrix_sha256'] and all(digest(V/p,False)==h for p,h in x['source_compact_sha256'].items()))
visual_beta=read('beta-crossing-visual-review.json');volume_beta=read('beta-crossing-volume-visual-review.json')
r=read('beta-crossing-raster-comparison.json');c=read('beta-crossing-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['beta-crossing-combined-review-coverage']=(x['pdf_sha256']==visual_beta['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_higher['pdf_sha256'] and x['page_count']==527 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==516 and len(fresh)==11 and not matched&fresh and matched|fresh==set(range(1,528)) and len(reviewed)==9 and not reviewed&set(visual_beta['full_pages_reviewed']) and reviewed|set(visual_beta['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_beta['full_pages_reviewed'])
outcomes['beta-crossing-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==551 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==17 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_beta['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_higher['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_beta['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_beta['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_beta['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


x=read('S6-convergent-splits-matrix.json');y=read('S6-convergent-splits-native-search.json')
outcomes['S6-complete-convergent-modular-search-scope']=(y['status']=='SEARCH_DIAGNOSTIC' and y['rows']==x['rows']==16603 and y['columns']==x['columns']==8786 and y['common_denominator']==x['common_denominator']==5760 and y['prime']==2147483647 and y['rank']==4985 and not y['target_modular_member'] and y['residual_term_count_is_partial'] and y['matrix_sha256']==x['matrix_sha256'] and y['source_compact_sha256']==x['source_compact_sha256'] and digest(V/'s6_modular_solver.cpp',True)==y['source_cpp_sha256'])


# Preserved seventeenth/eighteenth intake and fresh full mathematical replays.
for part,archives_count,members,originals in [('seventeenth',5,187,190),('eighteenth',6,267,270)]:
    x=read(part+'-incoming-retirement.json')
    outcomes[part+'-archive-retirement']=(x['archive_count']==archives_count and x['preserved_members']==members and x['original_members']==originals and x['archive_only_members']==3 and len(x['archives'])==archives_count and all(a['retired'] and not (B.parents[3]/a['archive']).exists() and a['arrival_commit']==archive_by_path[a['archive']]['archive_git_revision'] and a['members']==len(archive_by_path[a['archive']]['files']) for a in x['archives']))
for intake,parts in [('seventeenth',[('alternating',1),('determinants',3),('quadratic',2),('spectral',2),('quartic',1)]),('eighteenth',[('affine',1),('bernoulli',1),('bilinear',8),('dougall',4),('boundary',4),('vertical',1)])]:
    for part,count in parts:
        x=read(f'{intake}-replay/{part}/replay-summary.json');folder=B.parent/'reports'/x['source_folder']
        outcomes[intake+'-full-mathematical-replay/'+part]=(x['passed'] and len(x['commands'])==count and all(c['exit_code']==0 for c in x['commands']) and bool(x['fresh_result_files']) and all((V/(intake+'-replay')/part/p).is_file() for p in x['fresh_result_files']) and all(digest(folder/p,False)==h for p,h in x['source_code_sha256'].items()))
x=read('eighteenth-replay/boundary/verification/tails/run_tail_checks_full.json')
outcomes['order-twelve-complete-fresh-native-and-Python-replay']=(x['all_checks_passed'] and x['full_replay'] and x['order_twelve_case_count']==11513 and x['inherited_source_hashes_verified']==14 and x['order_ten_recorded_results_preserved'] and x['order_twelve_complete_residue_list_preserved'] and all(c['exit_code']==0 for c in x['checks']))
x=read('prefix-normalization-exact.json')
outcomes['prefix-original-retained-exact-normalization']=(x['status']=='PASS' and not x['imports_delivered_code'] and [(r['a'],r['b']) for r in x['normalization_checks']]==[(5,10),(6,12),(7,14),(7,15),(7,16)] and all(r['passed'] and r['wrong_sign_rejected'] and Fraction(r['original_determinant'])==Fraction(r['exact_multiplier'])*Fraction(r['retained_determinant'])!=0 for r in x['normalization_checks']))
outcomes['order-fourteen-complete-ordinary-identity-compiler']=(x['example_tail_orders']==[14,16] and x['both_example_inverse_products'] and len(x['ordinary_identity_rows'])==8 and [r['k'] for r in x['ordinary_identity_rows']]==list(range(8)) and all(len(r['even_weight_coefficients'])==16 for r in x['ordinary_identity_rows']))
x=read('prefix-order-fourteen/rank14-completion-replay.json');t=read('prefix-order-fourteen/eventual_threshold_checks.json')['cases'][0]
outcomes['order-fourteen-complete-exact-finite-certificate']=(x['status']=='PASS' and x['a']==7 and x['p']==14 and x['prime']==7340033 and x['sufficient_B']==80640 and x['first_b']==8 and x['last_b']==80639 and x['finite_cases']==80632 and x['zero_determinants']==0 and x['all_case_residues_match'] and x['Bernoulli_coefficients_checked']==161281 and x['independent_Bernoulli_tables_match'] and x['preserved_payloads_reproduced'] and x['integer_convolution_max_bound']<2**64 and x['laplace_signed_int64_bound']<2**63 and digest(V/'prefix-order-fourteen/rank14-residues-native.bin',False)==x['native_residue_sha256'] and digest(V/'prefix-order-fourteen/rank14_scan.cpp',True)==x['native_source_sha256'])
outcomes['order-fourteen-exact-eventual-threshold-instance']=(t['a']==7 and t['p']==14 and t['sufficient_B']==t['B0']==80640 and t['e']==56 and t['g']==658 and t['L']==144 and t['factorial_cancellation_checks']==196 and t['all_exact_checks_passed'] and t['scaled_entry_norm_E']<2**315)
x=read('prefix-order-ten/replay/replay-summary.json');e=read('prefix-order-ten/replay/order-ten-exception-probe.json');n=read('prefix-order-ten/replay/order-ten-exception-native.json')
outcomes['order-ten-independent-rational-and-Wolfram-exception']=(x['status']=='PASS' and x['all_processes_exit_zero'] and all(digest(V/'prefix-order-ten'/p,True)==h for p,h in x['source_code_sha256'].items()) and e['status']=='PASS' and e['a']==n['a']==5 and e['b']==n['b']==962 and e['two_exact_entry_constructions_agree'] and e['both_inverse_products'] and e['determinant_nonzero'] and Fraction(e['determinant'])!=0 and n['all_pass'] and n['exact_rational_arithmetic'] and len(n['checks'])==6 and all(n['checks'].values()))


visual_optimal=read('optimal-prefix-visual-review.json');volume_optimal=read('optimal-prefix-volume-visual-review.json')
r=read('optimal-prefix-raster-comparison.json');c=read('optimal-prefix-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['optimal-prefix-combined-review-coverage']=(x['pdf_sha256']==visual_optimal['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_beta['pdf_sha256'] and x['page_count']==536 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and not matched&fresh and matched|fresh==set(range(1,537)) and not reviewed&set(visual_optimal['full_pages_reviewed']) and reviewed|set(visual_optimal['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_optimal['full_pages_reviewed'])
outcomes['optimal-prefix-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])+sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==577 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_optimal['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_beta['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_optimal['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_optimal['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_optimal['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


# Nineteenth intake: original evidence and complete isolated replays.
x=read('nineteenth-incoming-retirement.json')
outcomes['nineteenth-archive-retirement']=(x['archive_count']==12 and x['preserved_members']==429 and x['original_members']==433 and x['archive_only_members']==4 and len(x['archives'])==12 and all(a['retired'] and not (B.parents[3]/a['archive']).exists() and a['arrival_commit']==archive_by_path[a['archive']]['archive_git_revision'] and a['members']==len(archive_by_path[a['archive']]['files']) for a in x['archives']))
for part,count in [('balanced',4),('boundary',1),('connected',3),('colored',7),('gap-six',1),('lattice',1),('selectors',3),('order-ten',1),('ordered',1),('joint',8),('universal',4),('beta',2)]:
    x=read(f'nineteenth-replay/{part}/replay-summary.json');folder=B.parent/'reports'/x['source_folder']
    outcomes['nineteenth-full-mathematical-replay/'+part]=(x['passed'] and len(x['commands'])==count and all(c['exit_code']==0 for c in x['commands']) and bool(x['fresh_result_files']) and all((V/'nineteenth-replay'/part/p).is_file() for p in x['fresh_result_files']) and all(digest(folder/p,False)==h for p,h in x['source_code_sha256'].items()) and (part=='lattice' or not x.get('copy_only_repairs',[])))
x=read('nineteenth-replay/lattice/replay-summary.json');f=read('nineteenth-replay/lattice-unmodified-failure/failure-summary.json');repairs=x['copy_only_repairs']
outcomes['lattice-original-failure-and-qualified-writer-repair']=(f['status']=='FAILED_ORIGINAL_RECEIPT_WRITER' and f['exit_code']==1 and not f['mathematical_change'] and len(f['fresh_before_failure'])==2 and len(repairs)==1 and repairs[0]['path']=='verification/check_mixed_tails_numeric.py' and repairs[0]['original_source_sha256']==x['source_code_sha256'][repairs[0]['path']] and (V/'nineteenth-replay/lattice-unmodified-failure/1-run.txt').is_file() and (V/'nineteenth-replay/lattice/receipt-path-copy-only.patch').is_file())
x=read('nineteenth-replay/universal/data/universal_checks.json')
outcomes['all-index-Gamma-supplied-complete-coefficient-replay']=(x['result']=='PASS' and x['maximum_weight']==30 and x['coefficient_comparisons']==28629 and x['nonzero_coefficients']==2974 and x['maximum_derivative_index_checked']==14)
x=read('nineteenth-replay/beta/data/exact_checks.json');c=x['counts']
outcomes['all-index-beta-independent-complete-coefficient-replay']=(x['status']=='PASS' and x['maximum_weight']==32 and c['coefficient_comparisons']==8350 and c['support_sign_checks']==8317 and c['primitive_identities']==29 and c['homotopy_comparisons']==19 and c['appell_checks']==32 and c['mixed_square_checks']==1684 and c['corruption_controls']==2)
x=read('alpha-five-exact.json');n=read('alpha-five-native.json')
outcomes['corrected-fifth-Gamma-exact-and-native-coefficient']=(x['status']=='PASS' and x['degree']==n['degree']==5 and x['independent_exponential_and_differentiated_recurrence_agree'] and x['printed_equation_matches_verified_coefficient'] and x['wrong_self_referential_term_rejected'] and x['repeated_readme_passage_count']==1 and not x['imports_delivered_code'] and n['all_pass'] and n['exact_symbolic_arithmetic'] and all(n['checks'].values()))
x=read('analytic-normal-generator-checks.json')
outcomes['analytic-normal-generator-independent-exact-coefficients']=(x['status']=='PASS' and not x['imports_delivered_code'] and x['exact_coefficient_comparisons']==1596 and x['weights']==[0,18] and [r['weight'] for r in x['normalization_checks']]==list(range(1,19)) and all(r['passed'] for r in x['normalization_checks']) and x['endpoint_polynomial_bounds_checked']==24 and x['affine_coefficient_checks']==19)
outcomes['analytic-normal-generator-independent-ordinary-diagnostics']=(x['working_digits']==75 and not x['interval_certified'] and len(x['numerical_diagnostics'])==20 and all(r['passed'] and Decimal(r['series_error'])<Decimal('1e-25') and Decimal(r['finite_projection_difference'])<=Decimal(r['proved_tail_majorant']) for r in x['numerical_diagnostics']))
outcomes['affine-entire-normal-generator-and-subtraction-control']=(len(x['affine_closed_generator_diagnostics'])==2 and all(r['passed'] and Decimal(r['error'])<Decimal('1e-70') for r in x['affine_closed_generator_diagnostics']) and x['missing_linear_subtraction_control']['rejected'] and x['missing_linear_subtraction_control']['correct_coefficient']=='0' and Decimal(x['missing_linear_subtraction_control']['wrong_unique_u2_coefficient'])>0)


visual_nineteenth=read('nineteenth-visual-review.json');volume_nineteenth=read('nineteenth-volume-visual-review.json')
r=read('nineteenth-raster-comparison.json');c=read('nineteenth-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['nineteenth-combined-review-coverage']=(x['pdf_sha256']==visual_nineteenth['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_optimal['pdf_sha256'] and x['page_count']==540 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==531 and len(fresh)==9 and not matched&fresh and matched|fresh==set(range(1,541)) and len(reviewed)==7 and not reviewed&set(visual_nineteenth['full_pages_reviewed']) and reviewed|set(visual_nineteenth['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_nineteenth['full_pages_reviewed'])
outcomes['nineteenth-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==570 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==11 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_nineteenth['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_optimal['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_nineteenth['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_nineteenth['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_nineteenth['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


# Twentieth intake: source preservation, full qualified replays and independent primitives.
x=read('twentieth-incoming-retirement.json')
outcomes['twentieth-archive-retirement']=(x['archive_count']==5 and x['preserved_members']==165 and x['original_members']==169 and x['archive_only_members']==4 and len(x['archives'])==5 and all(a['retired'] and not (B.parents[3]/a['archive']).exists() and a['arrival_commit']==archive_by_path[a['archive']]['archive_git_revision'] and a['members']==len(archive_by_path[a['archive']]['files']) for a in x['archives']))
for part,count in [('cubic',4),('higher',2),('anchors',1),('hankel',1),('universal',2)]:
    x=read(f'twentieth-replay/{part}/replay-summary.json');folder=B.parent/'reports'/x['source_folder']
    outcomes['twentieth-full-mathematical-replay/'+part]=(x['passed'] and len(x['commands'])==count and all(c['exit_code']==0 for c in x['commands']) and bool(x['fresh_result_files']) and all((V/'twentieth-replay'/part/p).is_file() for p in x['fresh_result_files']) and all(digest(folder/p,False)==h for p,h in x['source_code_sha256'].items()) and (part=='higher' or not x['copy_only_repairs']))
x=read('twentieth-replay/higher/replay-summary.json');r=read('twentieth-replay/higher/checks/reproduction_exact_numeric.json')
f=read('twentieth-replay/higher-unmodified-failure/failure-summary.json');g=read('twentieth-replay/higher-serialization-metadata-failure/failure-summary.json')
outcomes['higher-identities-preserved-failures-and-qualified-structured-comparison']=(not f['passed'] and not f['remaining_checks_passed'] and not g['passed'] and len(x['copy_only_repairs'])==1 and x['copy_only_repairs'][0]['path']=='reproduce.py' and x['copy_only_repairs'][0]['original_source_sha256']==x['source_code_sha256']['reproduce.py'] and (V/'twentieth-replay/higher/structured-record-copy-only.patch').is_file() and (V/'twentieth-replay/higher-unmodified-failure/1-run.txt').is_file() and (V/'twentieth-replay/higher-serialization-metadata-failure/1-run.txt').is_file() and r['requested']=={'exact':True,'numeric':True} and r['status']=='all requested checks passed' and all(c.get('exit_code',0)==0 and c.get('exact_match',True) for c in r['checks']))
# The complete CSV is reproduced by the wrapper; its independent log is JSON
# and reports all exact fields except the descriptive byte identifier.
x=json.loads((V/'twentieth-replay/higher-serialization-metadata-failure/fresh-checks/gap_ten_independent.log').read_text(encoding='utf-8'))
y=json.loads((B.parent/'reports/stieltjes-harmonic-resonance/continuations/higher-identities/code/gap_ten/gap_ten_independent_checks.json').read_text(encoding='utf-8'))
# The wrapper compares the full regenerated JSON with this immutable record;
# its console summary intentionally omits the thirteen expanded matrix rows.
outcomes['gap-ten-full-finite-coverage-and-independent-boundary-checks']=(x['half_gap']==5 and x['analytic_threshold']==73728 and x['finite_range']==[6,73727] and x['nonzero_residues']==73722 and x['prime']==998244353 and x['independent_direct_recurrence_determinants']==506 and x['independent_Bernoulli_coefficients']==64 and x['all_checks_passed'] and len(y['original_source_matrix_checks'])==13 and any(c['name']=='record:code/gap_ten/gap_ten_independent_checks.json' and c['exact_match'] for c in r['checks']))
x=read('twentieth-replay/anchors/results/exact.json')
outcomes['mixed-tail-anchors-complete-exact-replay']=(x['status']=='passed' and x['number_of_checks']==369)
x=read('twentieth-replay/cubic/verification/exact_results.json')
outcomes['cubic-normal-complete-exact-replay']=(x['status']=='PASS' and x['exact_checks']['normal_decomposition']==31)
x=read('primitive-homotopy-checks.json')
outcomes['primitive-homotopy-independent-exact-and-affine-coefficients']=(x['status']=='PASS' and not x['imports_delivered_code'] and x['weights']==[0,18] and [r['weight'] for r in x['exact_weight_checks']]==list(range(19)) and all(r['passed'] for r in x['exact_weight_checks']) and len(x['affine_coefficients'])==19 and all(r['passed'] for r in x['affine_coefficients']) and x['generic_Euler_boundary_monomials']>100 and x['factor_degree_division_control_rejected'] and x['primitive_Appell_identity_with_weight_two_anomaly'])
outcomes['primitive-affine-generator-and-required-constant-control']=(x['working_digits']==80 and not x['interval_certified'] and len(x['affine_closed_diagnostics'])==2 and all(r['passed'] and Decimal(r['error'])<Decimal('1e-40') for r in x['affine_closed_diagnostics']) and all(x['constant_normalization_control'][k] for k in ['rejected_missing_t_over_two','printed_formula_bound']) and x['constant_normalization_control']['weight_one_primitive']=='0')
x=read('primitive-affine-native.json')
outcomes['primitive-affine-native-symbolic-identity-and-coefficients']=(x['all_pass'] and x['exact_symbolic_arithmetic'] and x['coefficient_degrees']==[2,18] and len(x['checks'])==5 and all(x['checks'].values()))


visual_twentieth=read('twentieth-visual-review.json');volume_twentieth=read('twentieth-volume-visual-review.json')
r=read('twentieth-raster-comparison.json');c=read('twentieth-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['twentieth-combined-review-coverage']=(x['pdf_sha256']==visual_twentieth['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_nineteenth['pdf_sha256'] and x['page_count']==543 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==536 and len(fresh)==7 and not matched&fresh and matched|fresh==set(range(1,544)) and len(reviewed)==5 and not reviewed&set(visual_twentieth['full_pages_reviewed']) and reviewed|set(visual_twentieth['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_twentieth['full_pages_reviewed'])
outcomes['twentieth-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==575 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==9 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_twentieth['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_nineteenth['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_twentieth['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_twentieth['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_twentieth['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


x=read('primitive-coefficient-checks.json')
outcomes['every-primitive-coefficient-independent-complete-rational-replay']=(x['status']=='PASS' and not x['imports_delivered_code'] and x['maximum_weight']==30 and x['complete_coefficient_comparisons']==23025 and x['nonzero_support_sign_checks']==23024 and x['highest_index']==28 and [r['weight'] for r in x['weights']]==list(range(1,31)) and all(r['passed'] and (r['weight']==1 or r['nonzero']==r['compared']) for r in x['weights']) and all(x['controls'].values()))
outcomes['primitive-ordinary-E1-independent-projection-diagnostics']=(x['working_digits']==75 and not x['interval_certified'] and len(x['ordinary_projection_diagnostics'])==12 and all(r['passed'] and Decimal(r['error'])<Decimal('1e-25') for r in x['ordinary_projection_diagnostics']))
x=read('primitive-coefficient-native.json')
outcomes['every-primitive-coefficient-native-symbolic-defining-identities']=(x['all_pass'] and x['exact_symbolic_arithmetic'] and x['maximum_weight']==16 and len(x['checks'])==5 and all(x['checks'].values()) and [r['weight'] for r in x['rows']]==list(range(17)) and all(r['identity_passed'] for r in x['rows']))


visual_primitive=read('primitive-coefficients-visual-review.json');volume_primitive=read('primitive-coefficients-volume-visual-review.json')
r=read('primitive-coefficients-raster-comparison.json');c=read('primitive-coefficients-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['primitive-coefficients-combined-review-coverage']=(x['pdf_sha256']==visual_primitive['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_twentieth['pdf_sha256'] and x['page_count']==545 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==539 and len(fresh)==6 and not matched&fresh and matched|fresh==set(range(1,546)) and len(reviewed)==3 and not reviewed&set(visual_primitive['full_pages_reviewed']) and reviewed|set(visual_primitive['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_primitive['full_pages_reviewed'])
outcomes['primitive-coefficients-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==578 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==8 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_primitive['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_twentieth['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_primitive['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_primitive['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_primitive['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


x=read('rational-input-checks.json')
outcomes['rational-input-independent-exact-amplitude-coefficients']=(x['status']=='PASS' and not x['imports_delivered_code'] and x['maximum_weight']==30 and x['coefficient_comparisons']==120 and x['weighted_defining_identity_checks']==30 and [r['weight'] for r in x['rows']]==list(range(1,31)) and all(r['passed'] for r in x['rows']))
outcomes['rational-input-independent-dilogarithm-and-antiderivative-diagnostics']=(x['working_digits']==80 and not x['interval_certified'] and len(x['ODE_diagnostics'])==4 and all(r['passed'] and Decimal(r['linear_ODE_error'])<Decimal('1e-70') and Decimal(r['quadratic_ODE_error'])<Decimal('1e-70') for r in x['ODE_diagnostics']) and len(x['Taylor_diagnostics'])==2 and all(r['passed'] and Decimal(r['normal_error'])<Decimal('1e-35') and Decimal(r['primitive_error'])<Decimal('1e-35') for r in x['Taylor_diagnostics']) and len(x['antiderivative_diagnostics'])==2 and all(r['passed'] and Decimal(r['asinh_error'])<Decimal('1e-70') and Decimal(r['log_error'])<Decimal('1e-70') for r in x['antiderivative_diagnostics']))
x=read('rational-input-native.json')
outcomes['rational-input-native-symbolic-local-branches-and-closed-form-coefficients']=(x['all_pass'] and x['exact_symbolic_arithmetic'] and x['maximum_weight']==30 and len(x['checks'])==14 and all(x['checks'].values()))


visual_rational=read('rational-input-visual-review.json');volume_rational=read('rational-input-volume-visual-review.json')
r=read('rational-input-raster-comparison.json');c=read('rational-input-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['rational-input-combined-review-coverage']=(r['baseline_commit']=='64009dcd334e0190d1c00c6fc990a39112b4f99e' and x['pdf_sha256']==visual_rational['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_primitive['pdf_sha256'] and x['page_count']==547 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==visual_rational['inherited_reviewed_scientific_page_bodies'] and not matched&fresh and matched|fresh==set(range(1,548)) and len(reviewed)==visual_rational['exact_matching_fresh_volume_bodies'] and not reviewed&set(visual_rational['full_pages_reviewed']) and reviewed|set(visual_rational['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_rational['full_pages_reviewed'])
outcomes['rational-input-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==volume_rational['inherited_reviewed_scientific_page_bodies'] and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==volume_rational['full_pages_reviewed'] and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_rational['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_primitive['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_rational['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_rational['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_rational['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


x=read('hankel-alphabet-checks.json')
outcomes['hankel-alphabet-independent-confluent-grading-and-ensemble']=(x['status']=='PASS' and not x['imports_delivered_code'] and x['exact_allocation_cases']==2793 and x['formal_grading_cases']==32 and x['matrix_entry_checks']==240 and x['ensemble_checks']==360 and x['double_pole_Taylor_coefficients']==41 and len(x['grading'])==32 and all(r['passed'] and r['observed_weight']<=r['budget'] for r in x['grading']) and [r['cutoff'] for r in x['double_pole']]==list(range(41)) and all(r['passed'] for r in x['double_pole']) and len(x['corruption_controls'])==4 and all(x['corruption_controls'].values()))
outcomes['hankel-alphabet-ordinary-generator-and-endpoint-diagnostics']=(x['working_digits']==80 and not x['interval_certified'] and len(x['numeric_generators'])==3 and all(r['passed'] and r['terms']==800 and Decimal(r['error'])<Decimal('1e-70') for r in x['numeric_generators']) and Decimal(x['endpoint_error'])<Decimal('1e-65'))
x=read('hankel-alphabet-native.json')
outcomes['hankel-alphabet-native-symbolic-shifted-generator-and-cancellation']=(x['all_pass'] and x['exact_symbolic_arithmetic'] and x['maximum_cutoff']==30 and x['Taylor_coefficient_checks']==31 and len(x['checks'])==11 and all(x['checks'].values()))


x=read('twenty-first-incoming-retirement.json')
outcomes['twenty-first-archive-retirement']=(x['archive_count']==5 and x['preserved_members']==115 and x['original_members']==118 and x['archive_only_members']==3 and len(x['archives'])==5 and all(a['retired'] and not (B.parents[3]/a['archive']).exists() and a['arrival_commit']==archive_by_path[a['archive']]['archive_git_revision'] and a['members']==len(archive_by_path[a['archive']]['files']) and (B.parents[3]/a['destination']).is_dir() for a in x['archives']))
for part,count in [('normalized-resonant-jets',2),('resonant-inverse-folds',2),('sharp-dilog-reversion',2),('weighted-resonant-inversion',2),('order-jets-resonant-inversion',1)]:
    x=read('twenty-first-replay/'+part+'/replay-summary.json')
    outcomes['twenty-first-full-replay-'+part]=(x['passed'] and len(x['runs'])==count and all(r['exit_code']==0 for r in x['runs']))
x=read('twenty-first-replay/normalized-resonant-jets/fresh/exact_results.json')
y=read('twenty-first-replay/normalized-resonant-jets/fresh/extension_results.json')
outcomes['twenty-first-normalized-jets-exact-and-tuning']=(x['assertions_passed']==568 and y['exact_assertions_passed']==8 and y['numerical_comparisons_passed']==30 and len(y['tuning_rows'])==9)
x=read('twenty-first-replay/resonant-inverse-folds/fresh/exact_checks.json')
y=read('twenty-first-replay/resonant-inverse-folds/fresh/numeric_checks.json')
outcomes['twenty-first-inverse-fold-finite-checks']=(x['assertions']==150 and x['all_passed'] and all(r['passed'] for r in x['checks']) and y['all_passed'] and y['comparisons']==73 and y['precision_dps']==180 and all(r['passed'] for r in y['checks']))
x=read('twenty-first-replay/sharp-dilog-reversion/fresh/verification.json')
outcomes['twenty-first-sharp-dilog-full-pinned-diagnostics']=(x['status']=='passed' and x['numpy']=='2.3.5' and x['exact']['passed'] and x['exact']['assertions']==118 and len(x['borel_jets'])==3 and len(x['bell_jets'])==12 and len(x['periodic_kernels'])==6 and x['max_n']==256)
x=read('twenty-first-replay/weighted-resonant-inversion/fresh/verification.json')
outcomes['twenty-first-weighted-inverse-full-pinned-diagnostics']=(x['metadata']['versions']==x['metadata']['expected_versions'] and x['summary']['exact_resonance_cases']==16 and x['summary']['exact_generic_edge_families']==6 and len(x['numerical_jet_checks'])==24 and len(x['normal_form_checks'])==9 and len(x['critical_inverse_cases'])==27 and len(x['lambert_cases'])==4 and len(x['crossover_plot_grid'])==183 and Decimal(x['summary']['max_normalized_inverse_residual'])<Decimal('1e-60'))
x=read('twenty-first-replay/weighted-resonant-inversion-missing-dependency/replay-summary.json')
outcomes['twenty-first-original-dependency-failure-preserved']=(not x['passed'] and [r['exit_code'] for r in x['runs']]==[0,1] and 'ModuleNotFoundError' in (V/'twenty-first-replay/weighted-resonant-inversion-missing-dependency/2-verify.log').read_text(encoding='utf-8'))
x=read('twenty-first-replay/order-jets-resonant-inversion/fresh/run_summary.json')
y=read('twenty-first-replay/order-jets-resonant-inversion/fresh/borel_verification.json')
z=read('twenty-first-replay/order-jets-resonant-inversion/fresh/principal_sheet_check.json')
outcomes['twenty-first-order-jet-borel-and-principal-sheet-diagnostics']=(x['status']=='completed' and len(x['runs'])==4 and all(r['exit_code']==0 for r in x['runs']) and y['symbolic']['all_passed'] and y['numerical']['all_passed'] and len(y['numerical']['checks'])==4 and not y['numerical']['certified_interval_bounds'] and z['root']['Re_t_positive'] and Decimal(z['root']['modulus_z'])<1 and Decimal(z['integral_residual'])<Decimal('1e-75'))
x=read('resonant-ladder-checks.json')
outcomes['resonant-jet-ladder-and-finite-primitives']=(x['status']=='PASS' and not x['imports_delivered_code'] and x['exact_basis_cases']==3780 and x['exact_antiderivative_cases']==72 and len(x['numerical_rows'])==24 and x['working_digits']==85 and not x['interval_certified'] and all(Decimal(r['scaled_error'])<Decimal('1e-70') for r in x['numerical_rows']) and len(x['corruption_controls'])==3 and all(x['corruption_controls'].values()))

visual_hankel=read('hankel-alphabet-visual-review.json');volume_hankel=read('hankel-alphabet-volume-visual-review.json')
r=read('hankel-alphabet-raster-comparison.json');c=read('hankel-alphabet-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['hankel-alphabet-combined-review-coverage']=(r['baseline_commit']=='a24094ebd7e575bf8f8f0a0dad806a82e61688ad' and x['pdf_sha256']==visual_hankel['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_rational['pdf_sha256'] and x['page_count']==552 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==543 and not matched&fresh and matched|fresh==set(range(1,553)) and len(reviewed)==6 and not reviewed&set(visual_hankel['full_pages_reviewed']) and reviewed|set(visual_hankel['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_hankel['full_pages_reviewed'])
outcomes['hankel-alphabet-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==582 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==10 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_hankel['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_rational['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_hankel['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_hankel['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_hankel['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))

x=read('resonant-ladder-checks.json')
outcomes['resonant-jets-arbitrary-repeated-primitives']=(x['status']=='PASS' and x['exact_iterated_primitive_cases']==252)
x=read('resonant-primitives-native.json')
outcomes['resonant-jets-native-Gamma-ladder-and-endpoints']=(x['all_pass'] and x['exact_symbolic_arithmetic'] and len(x['checks'])==9 and all(x['checks'].values()))


visual_rj=read('resonant-jets-visual-review.json');volume_rj=read('resonant-jets-volume-visual-review.json')
r=read('resonant-jets-raster-comparison.json');c=read('resonant-jets-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['resonant-jets-combined-review-coverage']=(r['baseline_commit']=='1d7eae2e8b61fdd4306154b2b893691ee183aa24' and x['pdf_sha256']==visual_rj['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_hankel['pdf_sha256'] and x['page_count']==557 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==543 and not matched&fresh and matched|fresh==set(range(1,558)) and len(reviewed)==8 and not reviewed&set(visual_rj['full_pages_reviewed']) and reviewed|set(visual_rj['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_rj['full_pages_reviewed'])
outcomes['resonant-jets-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==585 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==15 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_rj['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_hankel['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_rj['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_rj['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_rj['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


x=read('feedback-bessel-checks.json')
outcomes['feedback-finite-Bessel-and-order-spectrum']=(x['passed'] and not x['imports_delivered_code'] and x['polylog_original_equation_coefficients']==240 and x['general_signed_kernel_coefficients']==120 and x['bessel_weight_recurrences']==450 and x['exact_spectral_shift_cases']==50 and len(x['corruption_controls'])==3 and all(x['corruption_controls'].values()))
feedback_report=B.parents[2]/'Transseries/docs/series-and-transseries/Quadratic_Polylogarithm_Feedback_Boundary_Completion'
x=json.loads((feedback_report/'intake-verification/receipt-checks.json').read_text())
outcomes['feedback-full-incoming-suite-replay']=(x['passed'] and len(x['recorded_outcomes'])==14 and all(x['recorded_outcomes'].values()) and Decimal(x['maximum_joint_real_relative_residual'])<Decimal('1e-100'))
x=read('twenty-second-incoming-archives.json')[0]
outcomes['twenty-second-delivery-retirement']=(x['original_member_count']==40 and len(x['files'])==39 and len(x['archive_only_members'])==1 and not (B.parents[3]/x['archive']).exists() and (B.parents[3]/'docs/incoming/README.md').is_file())


visual_fb=read('feedback-bessel-visual-review.json');volume_fb=read('feedback-bessel-volume-visual-review.json')
r=read('feedback-bessel-raster-comparison.json');c=read('feedback-bessel-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['feedback-bessel-combined-review-coverage']=(r['baseline_commit']=='55035067d3530f3fbe78e279b0f32c690ad76320' and x['pdf_sha256']==visual_fb['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_rj['pdf_sha256'] and x['page_count']==562 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==548 and not matched&fresh and matched|fresh==set(range(1,563)) and len(reviewed)==8 and not reviewed&set(visual_fb['full_pages_reviewed']) and reviewed|set(visual_fb['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_fb['full_pages_reviewed'])
outcomes['feedback-bessel-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==593 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==12 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_fb['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_rj['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_fb['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_fb['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_fb['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


x=read('lambert-moment-checks.json')
outcomes['Lambert-Gamma-moment-identities']=(x['passed'] and not x['imports_delivered_code'] and x['symbolic_polynomials']==9 and x['derivative_recurrences']==8 and x['exact_pole_orders']==5 and x['pole_diagnostic_A']=='2' and len(x['corruption_controls'])==4 and all(x['corruption_controls'].values()))
outcomes['Lambert-Laplace-and-convolution-quadrature']=(len(x['quadrature'])==2 and [a['decimal_precision'] for a in x['quadrature']]==[60,90] and all(a['laplace_cases']==12 and a['convolution_cases']==9 and Decimal(a['maximum_laplace_relative_error'])<Decimal('1e-45') and Decimal(a['maximum_convolution_relative_error'])<Decimal('1e-45') for a in x['quadrature']))


visual_lmi=read('lambert-moments-visual-review.json');volume_lmi=read('lambert-moments-volume-visual-review.json')
r=read('lambert-moments-raster-comparison.json');c=read('lambert-moments-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['Lambert-combined-review-coverage']=(r['baseline_commit']=='047d3d0a66d860adb160e133daec8256703b6c8a' and x['pdf_sha256']==visual_lmi['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_fb['pdf_sha256'] and x['page_count']==566 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==553 and not matched&fresh and matched|fresh==set(range(1,567)) and len(reviewed)==7 and not reviewed&set(visual_lmi['full_pages_reviewed']) and reviewed|set(visual_lmi['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_lmi['full_pages_reviewed'])
outcomes['Lambert-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==598 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==11 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_lmi['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_fb['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_lmi['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_lmi['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_lmi['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


x=read('mixed223-checks.json')
outcomes['mixed223-exact-polynomial-certificates']=(x['passed'] and not x['imports_delivered_code'] and x['coefficient_columns']==12 and x['first_minor']=='1/12600' and len(x['certificates'])==9 and len(x['dimensions'])==12 and all(a['dimension']==max(0,i-2) and a['maximum_P_degree']==5+2*i for i,a in enumerate(x['dimensions'])) and x['endpoint_coefficients']['0']=='-4037/108' and all(x['endpoint_coefficients'][str(k)]=='0' for k in range(-7,0)) and len(x['corruption_controls'])==4 and all(x['corruption_controls'].values()))
outcomes['mixed223-ordinary-partial-sums']=(len(x['numerical'])==2 and [a['decimal_precision'] for a in x['numerical']]==[70,100] and all(a['partial_sum_cases']==3 and Decimal(a['maximum_absolute_error'])<Decimal('1e-45') and len(a['endpoint_checks'])==3 for a in x['numerical']))


visual_mtt=read('mixed223-visual-review.json');volume_mtt=read('mixed223-volume-visual-review.json')
r=read('mixed223-raster-comparison.json');c=read('mixed223-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['mixed223-combined-review-coverage']=(r['baseline_commit']=='4df2ed344e6e35517b5b509df258b8a8cbc9763b' and x['pdf_sha256']==visual_mtt['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_lmi['pdf_sha256'] and x['page_count']==570 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==562 and not matched&fresh and matched|fresh==set(range(1,571)) and len(reviewed)==4 and not reviewed&set(visual_mtt['full_pages_reviewed']) and reviewed|set(visual_mtt['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_mtt['full_pages_reviewed'])
outcomes['mixed223-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==603 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==10 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_mtt['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_lmi['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_mtt['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_mtt['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_mtt['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


x=read('lambert-late-checks.json')
outcomes['Lambert-late-exact-correction-compiler']=(x['passed'] and not x['imports_delivered_code'] and x['maximum_correction']==4 and x['exact_faulhaber_product_checks']==65 and x['first_two_corrections_match'] and len(x['positive_action_polynomials'])==5)
outcomes['Lambert-late-full-finite-diagnostics']=(len(x['diagnostics'])==40 and max(a['n'] for a in x['diagnostics'])==201 and all(len(a['absolute_errors'])==5 for a in x['diagnostics']))
coefficient_source=B.parents[2]/'Transseries/docs/series-and-transseries/Resonant_Lambert_Inverse_Transseries/continuations/summation-singularities/intake-verification/lambert_checks.json'
outcomes['Lambert-late-independent-coefficient-input']=(coefficient_source.read_bytes()==(V/'lambert-late-finite-coefficients.json').read_bytes() and len(read('lambert-late-finite-coefficients.json')['rows'])==40)
x=read('twenty-third-incoming-archives.json')+read('twenty-fourth-incoming-archives.json')
outcomes['recent-Lambert-intake-preserved-and-retired']=(len(x)==4 and sum(len(a['files']) for a in x)==75 and sum(a['original_member_count'] for a in x)==76 and all(not (B.parents[3]/a['archive']).exists() for a in x))


visual_llc=read('lambert-late-visual-review.json');volume_llc=read('lambert-late-volume-visual-review.json')
r=read('lambert-late-raster-comparison.json');c=read('lambert-late-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['lambert-late-combined-review-coverage']=(r['baseline_commit']=='ce0052e960ed6d0680980beb69f551dae66673ed' and x['pdf_sha256']==visual_llc['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_mtt['pdf_sha256'] and x['page_count']==575 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==561 and not matched&fresh and matched|fresh==set(range(1,576)) and len(reviewed)==7 and not reviewed&set(visual_llc['full_pages_reviewed']) and reviewed|set(visual_llc['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_llc['full_pages_reviewed'])
outcomes['lambert-late-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==606 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==12 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_llc['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_mtt['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_llc['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_llc['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_llc['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


continuation_home=B.parents[2]/'Transseries/docs/series-and-transseries/Resonant_Lambert_Inverse_Transseries/continuations/late-coefficients'
x=json.loads((continuation_home/'intake-verification/results.json').read_text())
e=json.loads((continuation_home/'intake-verification/exact_results.json').read_text())
outcomes['Lambert-continuation-fresh-exact-replay']=(e['status']==x['status']=='passed' and e['assertions']==x['exact_assertions']==5890 and e['formal_order']==x['exact_order']==12)
outcomes['Lambert-continuation-full-finite-replay']=(x['main_diagnostic_count']==len(x['diagnostics'])==70 and max(x['indices'])==1025 and all(a['complete_finite_sum'] and a['k_max']==a['n'] for a in x['diagnostics']) and x['reproducibility']['longdouble_significand_bits']==64 and x['reproducibility']['longdouble_max_binary_exponent']==16384 and len(x['largest_index_improvements'])==14)
h=x['high_precision_crosschecks']
outcomes['Lambert-continuation-independent-80-digit-checks']=(h['status']=='passed' and h['mpmath_decimal_digits']==80 and len(h['records'])==35 and sum('exact_polynomial_crosscheck_error' in a for a in h['records'])==15 and Decimal(h['max_extended_precision_error'])<Decimal('2e-15') and Decimal(h['max_exact_polynomial_error'])<Decimal('1e-68'))
a=read('twenty-fifth-incoming-archives.json')
outcomes['Lambert-continuation-source-retired']=(len(a)==3 and len(a[0]['files'])==27 and a[0]['original_member_count']==28 and not (B.parents[3]/a[0]['archive']).exists())


visual_lbc=read('lambert-continuation-visual-review.json');volume_lbc=read('lambert-continuation-volume-visual-review.json')
r=read('lambert-continuation-raster-comparison.json');c=read('lambert-continuation-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['lambert-continuation-combined-review-coverage']=(r['baseline_commit']=='1cd65680c3378bfdf60fe18015b74af278781dee' and x['pdf_sha256']==visual_lbc['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_llc['pdf_sha256'] and x['page_count']==578 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==564 and not matched&fresh and matched|fresh==set(range(1,579)) and len(reviewed)==6 and not reviewed&set(visual_lbc['full_pages_reviewed']) and reviewed|set(visual_lbc['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_lbc['full_pages_reviewed'])
outcomes['lambert-continuation-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==609 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==15 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_lbc['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_llc['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_lbc['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_lbc['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_lbc['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


x=read('neutral-inverse-coefficients.json')
outcomes['neutral-inverse-exact-coefficients']=(x['passed'] and x['maximum_degree']==5 and x['composition_coefficients_checked']==5 and len(x['coefficients'])==5 and len(x['corruption_controls'])==4 and all(x['corruption_controls'].values()))
ojf_home=B.parents[2]/'Transseries/docs/series-and-transseries/Resonant_Polylogarithm_Transseries/continuations/order-jet-filters'
for directory in ['intake-verification','intake-verification-local']:
    groups=[json.loads((ojf_home/directory/(n+'.json')).read_text()) for n in ['exact','stieltjes','borel','neutral','large_inverse','small_inverse']]
    outcomes['order-filter-'+directory+'-replay']=(all(a['status']=='PASS' and a['dps']==70 for a in groups) and sum(a['exact_assertions'] for a in groups)==165 and sum(a['numerical_assertions'] for a in groups)==46)
x=read('neutral-inverse-experiment.json')
outcomes['neutral-inverse-independent-diagnostics']=(x['status']=='passed' and x['dps']==75 and len(x['records'])==6 and {(a['m'],a['w']) for a in x['records']}=={(m,w) for m in [0,1,2] for w in ['10.0','20.0']} and all(a['N']==1 and abs(Decimal(a['ratio'])-1)<Decimal('.001') and Decimal(a['cauchy_refinement_error'])<Decimal('1e-45') and Decimal(a['neutral_residual'])<Decimal('1e-65') and Decimal(a['scaled_inverse_residual'])<Decimal('1e-45') for a in x['records']))


visual_ojf=read('order-filters-visual-review.json');volume_ojf=read('order-filters-volume-visual-review.json')
r=read('order-filters-raster-comparison.json');c=read('order-filters-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['order-filters-combined-review-coverage']=(r['baseline_commit']=='867c044b309aefe34534fe9656148cf460432236' and x['pdf_sha256']==visual_ojf['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_lbc['pdf_sha256'] and x['page_count']==595 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==569 and not matched&fresh and matched|fresh==set(range(1,596)) and len(reviewed)==20 and not reviewed&set(visual_ojf['full_pages_reviewed']) and reviewed|set(visual_ojf['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_ojf['full_pages_reviewed'])
outcomes['order-filters-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==617 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==24 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_ojf['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_lbc['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_ojf['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_ojf['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_ojf['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))


x=read('matched-endpoint-identities.json')
outcomes['matched-endpoint-exact-transport']=(x['passed'] and len(x['exact_transport_identities'])==24 and all(r['passed'] for r in x['exact_transport_identities']) and x['central_H5_order_derivative']==-4 and len(x['corruption_controls_detected'])==4 and all(x['corruption_controls_detected']))
outcomes['matched-endpoint-independent-fourier']=(x['fourier_dps']==75 and len(x['fourier_comparisons'])==9 and all(r['passed'] and Decimal(r['absolute_difference'])<Decimal('1e-60') for r in x['fourier_comparisons']))
x=read('matched-endpoint-coefficients.json')
outcomes['matched-endpoint-finite-coefficients']=(x['passed'] and x['dps']==65 and len(x['records'])==21 and sum(r['central_sign'] is True for r in x['records'])==7 and all(Decimal(r['scale_residual'])<Decimal('1e-55') for r in x['records']))
outcomes['matched-endpoint-precision-refinement']=(x['refinement_dps']==85 and len(x['precision_refinements'])==9 and all(r['passed'] and Decimal(r['absolute_difference'])<Decimal('1e-42') for r in x['precision_refinements']))
jct_home=B.parents[2]/'Transseries/docs/series-and-transseries/Quadratic_Polylogarithm_Feedback_Boundary_Completion/continuations/joint-coefficient-transseries/intake-verification'
x=json.loads((jct_home/'symbolic_validation.json').read_text(encoding='utf-8'))
outcomes['joint-coefficient-source-symbolic-replay']=(x['status']=='PASS' and all(len(x[k])==n and all(r['exact_residual']=='0' for r in x[k]) for k,n in [('stirling_expansion_checks',6),('central_gamma_checks',36),('marginal_identity_checks',5)])) and len(x['kernel_closed_form_checks'])==9 and all(Decimal(r['absolute_error'])<Decimal('1e-60') for r in x['kernel_closed_form_checks'])
x=json.loads((jct_home/'coefficient_validation.json').read_text(encoding='utf-8'))
outcomes['joint-coefficient-source-finite-replay']=(x['exact_original_equation_check']['original_equation_equals_lagrange_exactly'] and x['exact_original_equation_check']['degree']==8 and len(x['rows'])==36 and not x['interval_certified'] and len(x['parabolic_cylinder_vs_fourier_checks'])==3 and all(Decimal(r['absolute_difference'])<Decimal('1e-60') for r in x['parabolic_cylinder_vs_fourier_checks']))
x=json.loads((jct_home/'endpoint_diagnostics.json').read_text(encoding='utf-8'))
outcomes['joint-coefficient-source-endpoint-diagnostics']=(x['precision_dps']==80 and len(x['reciprocal_endpoint'])==9 and len(x['cut_modulus'])==6 and all(Decimal(r['scaled_modulus_difference'])<0 for r in x['cut_modulus']))


visual_jct=read('joint-coefficients-visual-review.json');volume_jct=read('joint-coefficients-volume-visual-review.json')
r=read('joint-coefficients-raster-comparison.json');c=read('joint-coefficients-cross-edition-review.json')
x=r['pdfs'][-1];matched={a['page'] for a in x['exact_matching_scientific_bodies']};fresh=set(x['changed_scientific_bodies']);reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['joint-coefficients-combined-review-coverage']=(r['baseline_commit']=='d1bb324841f697fb9d7345cb921e9c05a7bc38b8' and x['pdf_sha256']==visual_jct['pdf_sha256']==c['combined_pdf_sha256'] and x['previous_pdf_sha256']==visual_ojf['pdf_sha256'] and x['page_count']==616 and r['crop_bottom_points']==c['crop_bottom_points']==57 and r['excluded_content_is_only_centered_footer_page_numbers'] and c['excluded_content_is_only_centered_footer_page_numbers'] and len(matched)==586 and not matched&fresh and matched|fresh==set(range(1,617)) and len(reviewed)==23 and not reviewed&set(visual_jct['full_pages_reviewed']) and reviewed|set(visual_jct['full_pages_reviewed'])==fresh and c['remaining_full_pages_to_review']==visual_jct['full_pages_reviewed'])
outcomes['joint-coefficients-volume-review-coverage']=(sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==633 and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==29 and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies']) and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1)) and volume_jct['volumes'][i]['pdf_sha256']==x['pdf_sha256'] and x['previous_pdf_sha256']==volume_ojf['volumes'][i]['pdf_sha256'] and set(x['changed_scientific_bodies'])==set(volume_jct['volumes'][i]['full_pages_reviewed']) for i,x in enumerate(r['pdfs'][:4])) and all(a['reviewed_volume_page'] in volume_jct['volumes'][a['volume_number']-1]['full_pages_reviewed'] and a['pdf_sha256']==volume_jct['volumes'][a['volume_number']-1]['pdf_sha256'] for a in c['exact_matching_reviewed_bodies']))

x=read('check_stieltjes_reflection_algebra.json')
outcomes['stieltjes-reflection-finite-algebra']=(x['status']=='PASS' and len(x['exact_normal_forms'])==7 and x['polarized_generator_coefficients_two_branches']==56 and len(x['negative_controls'])==4 and all(x['negative_controls'].values()))
x=read('check_stieltjes_neutral_reflection.json')
outcomes['stieltjes-neutral-order-identities']=(x['status']=='PASS' and len(x['alternating_two_branch_checks'])==18 and all(r['exact_residual']=='0' for r in x['alternating_two_branch_checks']) and len(x['neutral_hyperplane_checks'])==6 and sum(len(r['degrees']) for r in x['neutral_hyperplane_checks'])==54 and all(all(v=='0' for v in r['exact_residuals']) for r in x['neutral_hyperplane_checks']) and len(x['negative_controls'])==3 and all(x['negative_controls'].values()))
x=read('check_stieltjes_mellin_exact.json')
outcomes['stieltjes-mellin-exact-reconstruction']=(x['all_passed'] and len(x['records'])==58 and all(r['residual']=='0' for r in x['records']) and len(x['rejected_negative_controls'])==4 and all(v!='0' for v in x['rejected_negative_controls'].values()))
x=read('check_stieltjes_mellin_numeric.json')
outcomes['stieltjes-digamma-and-mellin-quadratures']=(x['all_absolute_errors_below_1e-40'] and sum(len(g['rows']) for g in x['reconstruction'])==22 and sum(len(g['rows']) for g in x['raising'])==4 and len(x['resonances']['rows'])==18 and all(Decimal(r['absolute_error'])<Decimal('1e-40') for g in x['reconstruction']+x['raising']+[x['resonances']] for r in g['rows']))
a,b=x['reconstruction'][:2]
outcomes['stieltjes-digamma-precision-refinement']=(a['dps']==50 and b['dps']==70 and a['a']==b['a'] and a['b']==b['b'] and len(a['rows'])==len(b['rows'])==6 and all(r['n']==s['n'] and abs(Decimal(r['quadrature'])-Decimal(s['quadrature']))<Decimal('1e-40') for r,s in zip(a['rows'],b['rows'])))

r=read('stieltjes-reconstruction-raster-comparison.json');c=read('stieltjes-reconstruction-cross-edition-review.json')
x=r['pdfs'][-1]
matched={a['page'] for a in x['exact_matching_scientific_bodies']}
fresh=set(x['changed_scientific_bodies'])
reviewed={a['combined_page'] for a in c['exact_matching_reviewed_bodies']}
outcomes['stieltjes-reconstruction-combined-review-coverage']=(
    r['baseline_commit']=='0cdfdf14eff2e404ff3060ae7ca8048f251828a8'
    and x['pdf_sha256']==visual['pdf_sha256']==c['combined_pdf_sha256']
    and x['previous_pdf_sha256']==visual_jct['pdf_sha256'] and x['page_count']==623
    and r['crop_bottom_points']==c['crop_bottom_points']==57
    and r['excluded_content_is_only_centered_footer_page_numbers']
    and c['excluded_content_is_only_centered_footer_page_numbers']
    and len(matched)==visual['inherited_reviewed_scientific_page_bodies']
    and not matched&fresh and matched|fresh==set(range(1,624))
    and len(reviewed)==visual['exact_matching_fresh_volume_bodies']
    and not reviewed&set(visual['full_pages_reviewed'])
    and reviewed|set(visual['full_pages_reviewed'])==fresh
    and c['remaining_full_pages_to_review']==visual['full_pages_reviewed'])
outcomes['stieltjes-reconstruction-volume-review-coverage']=(
    sum(len(x['exact_matching_scientific_bodies']) for x in r['pdfs'][:4])==volume_visual['inherited_reviewed_scientific_page_bodies']
    and sum(len(x['changed_scientific_bodies']) for x in r['pdfs'][:4])==volume_visual['full_pages_reviewed']
    and all(not {a['page'] for a in x['exact_matching_scientific_bodies']}&set(x['changed_scientific_bodies'])
        and {a['page'] for a in x['exact_matching_scientific_bodies']}|set(x['changed_scientific_bodies'])==set(range(1,x['page_count']+1))
        and volume_visual['volumes'][i]['pdf_sha256']==x['pdf_sha256']
        and x['previous_pdf_sha256']==volume_jct['volumes'][i]['pdf_sha256']
        and set(x['changed_scientific_bodies'])==set(volume_visual['volumes'][i]['full_pages_reviewed'])
        for i,x in enumerate(r['pdfs'][:4]))
    and all(a['reviewed_volume_page'] in volume_visual['volumes'][a['volume_number']-1]['full_pages_reviewed']
        and a['pdf_sha256']==volume_visual['volumes'][a['volume_number']-1]['pdf_sha256']
        for a in c['exact_matching_reviewed_bodies']))

result=dict(changed_sources=changed,changed_dependencies=changed_dependencies,pdf_sha256=pdfhash,
 pdf_matches_build=pdfhash==build['pdf_sha256'],pdf_matches_render=pdfhash==render['pdf_sha256'],
 page_count=render['page_count'],source_documents=doc['source_documents'],converged_build=build['passed'],
 pdf_static_checks=render['static_passed'],document_integrity=doc['passed'],recorded_outcomes=outcomes,
 asymptotic_diagnostic_records=diagnostic_records,incoming_archive_errors=archive_errors,
 scope='Recorded evidence integrity only; visual review and scientific replay are separate activities.')
result['passed']=not changed and not changed_dependencies and all(outcomes.values()) and all(result[k] for k in ['pdf_matches_build','pdf_matches_render','converged_build','pdf_static_checks','document_integrity']) and result['page_count']==623 and result['source_documents']==1810 and render.get('pdf_author')=='ProveIt Contributors'
(V/'receipt-integrity.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2));raise SystemExit(0 if result['passed'] else 1)
