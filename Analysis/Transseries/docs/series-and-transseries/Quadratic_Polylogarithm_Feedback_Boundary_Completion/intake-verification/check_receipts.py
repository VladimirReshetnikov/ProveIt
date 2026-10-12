"""Check the finite recorded outcomes; this does not replay or prove theorems."""
from pathlib import Path
from decimal import Decimal
import json
B=Path(__file__).resolve().parent
def read(name): return json.loads((B/name).read_text(encoding='utf-8'))
def maximum(rows,key): return max(abs(Decimal(r[key])) for r in rows)
r=read('runner.json');f=read('feedback_verify/verification.json')
c=read('verify_coefficient_crossover/coefficient_crossover.json')
h=read('verify_critical_charts/critical_chart_checks.json')
t=read('verify_crossover/crossover_checks.json')
j=read('verify_joint_crossover/joint_crossover_checks.json')
checks={}
checks['five_full_processes']=r['all_processes_succeeded'] and len(r['suites'])==5 and all(x['exit_code']==0 for x in r['suites'])
checks['isolated_copy']=not r['originals_executed_in_place']
checks['eight_exact_original_equation_coefficients']=f['exact_rational_check']['degrees_checked']==8 and f['exact_rational_check']['all_original_equation_coefficients_equal_lagrange'] and f['exact_rational_check']['all_checked_coefficients_positive']
checks['independent_precision_comparison']=f['independent_precision_check']['agreement_within_tolerance'] and abs(Decimal(f['independent_precision_check']['relative_difference']))<Decimal(f['independent_precision_check']['acceptance_tolerance'])
checks['complete_phase_grid']=f['indices']==[128,512,2048] and len(f['coefficient_phase_rows'])==24
checks['complete_coefficient_crossover_grid']=len(c['rows'])==27 and all(Decimal(x['scaled_coefficient_Rb_power_n'])>0 for x in c['rows'])
checks['independent_stable_density_normalization']=len(c['density_normalization']['checks'])==3 and maximum(c['density_normalization']['checks'],'relative_difference')<Decimal('1e-14')
checks['critical_charts']=len(h['numeric_cases'])==12 and maximum(h['numeric_cases'],'scaled_equation_residual')<Decimal('1e-110') and h['symbolic_assertions']=='passed'
checks['critical_order_grid']=len(t['rows'])==9 and maximum(t['rows'],'original_relative_residual')<Decimal('1e-100') and maximum(t['rows'],'paired_relative_residual')<Decimal('1e-100')
checks['joint_real_grid']=len(j['real_cases'])==18 and maximum(j['real_cases'],'original_relative_residual')<Decimal('1e-100') and all(x['positive_root'] and x['positive_derivative_at_root'] for x in j['real_cases'])
folds=[x['interior_fold'] for x in j['real_cases'] if 'interior_fold' in x]
checks['negative_feedback_physical_branch']=len(folds)==6 and all(x['x_root_greater_than_x_fold'] and x['d_fold_negative'] for x in folds)
fold=j['local_complex_fold']
checks['local_complex_fold']=all(abs(Decimal(fold[k]))<Decimal('1e-140') for k in ['paired_equation_absolute_residual','paired_derivative_absolute_residual','original_relative_residual_absolute','original_derivative_residual_divided_by_z_absolute']) and Decimal(fold['fold_jacobian_absolute'])>1
checks['declared_versions']=f['environment']['numpy']=='2.3.5' and f['environment']['mpmath']=='1.3.0' and c['environment']['scipy']=='1.17.0'
checks['precision_scopes']=h['precision_decimal_digits']==180 and t['precision_decimal_digits']==200 and j['precision_decimal_digits']==180 and c['environment']['mpmath_digits']==75
row=next(x for x in f['coefficient_phase_rows'] if x['case']=='critical_s_3' and x['n']==2048)
result=dict(passed=all(checks.values()),recorded_outcomes=checks,leading_ratio_at_n2048=row['ratio_to_leading'],second_log_refinement_ratio_at_n2048=row['ratio_to_second_log_refinement'],maximum_joint_real_relative_residual=str(maximum(j['real_cases'],'original_relative_residual')),maximum_chart_scaled_residual=str(maximum(h['numeric_cases'],'scaled_equation_residual')),scope='Finite exact assertions and floating-point diagnostics only; not interval-certified or proof-assistant-checked. The proof audit is separate.')
(B/'receipt-checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
assert result['passed'], [k for k,v in checks.items() if not v]
