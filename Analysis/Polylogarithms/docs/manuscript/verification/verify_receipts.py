"""Verify the integrity and reported outcomes of the committed release evidence.

This reads pinned receipts; it does not rerun mathematics or perform visual QA.
"""
from pathlib import Path
from fractions import Fraction
from decimal import Decimal
import hashlib, json, sys, subprocess, io, zipfile
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
    'eighth-incoming-archives.json','ninth-incoming-archives.json']), [])
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
outcomes['incoming-archive-preservation']=len(archives)==47 and sum(len(a['files']) for a in archives)==1827 and not archive_errors
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
                     ('ninth', {'gauss':2,'mellin':9,'nested':1,'critical':1,'harmonic':1})]:
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
visual=read('visual-review.json')
outcomes['recorded-visual-review']=visual['passed'] and visual['pdf_sha256']==pdfhash and visual['page_count']==448 and visual['all_contact_sheets_reviewed']==28 and visual['scientific_figures_reviewed']==13 and not visual['findings']
result=dict(changed_sources=changed,changed_dependencies=changed_dependencies,pdf_sha256=pdfhash,
 pdf_matches_build=pdfhash==build['pdf_sha256'],pdf_matches_render=pdfhash==render['pdf_sha256'],
 page_count=render['page_count'],source_documents=doc['source_documents'],converged_build=build['passed'],
 pdf_static_checks=render['static_passed'],document_integrity=doc['passed'],recorded_outcomes=outcomes,
 asymptotic_diagnostic_records=diagnostic_records,incoming_archive_errors=archive_errors,
 scope='Recorded evidence integrity only; visual review and scientific replay are separate activities.')
result['passed']=not changed and not changed_dependencies and all(outcomes.values()) and all(result[k] for k in ['pdf_matches_build','pdf_matches_render','converged_build','pdf_static_checks','document_integrity']) and result['page_count']==448 and result['source_documents']==721 and render.get('pdf_author')=='ProveIt Contributors'
(V/'receipt-integrity.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2));raise SystemExit(0 if result['passed'] else 1)
