#!/usr/bin/env python3
"""Named source/schema mutations, fresh-directory replay, and actual hashes.
Every semantic or schema mutation must fail with its expected diagnostic in
both ordinary Python and python -O. A syntax error or unrelated crash fails
the campaign. No source fixture or validator is modified in place.
"""
import argparse
import ast
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

class CampaignError(Exception):
    pass

def require(condition, message):
    if not condition:
        raise CampaignError(message)

def digest(data):
    return sha256(data).hexdigest()

def execute(folder, optimized, group='all'):
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',LC_ALL='C',TZ='UTC')
    return subprocess.run([sys.executable]+(['-O'] if optimized else [])+
        [str(folder/'validate.py'),'--fixtures',str(folder/'fixtures.json'),'--only',group],
        cwd=folder,env=env,capture_output=True,text=True,timeout=180)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    home=Path(__file__).resolve().parent
    filenames=['fixtures.json','validate.py','mutation_campaign.py']
    before={name:digest((home/name).read_bytes()) for name in filenames}
    source=(home/'validate.py').read_text()
    fixture=(home/'fixtures.json').read_text()
    require(not any(isinstance(node,ast.Assert) for node in ast.walk(ast.parse(source))), 'Validator contains assert disabled by -O')
    cases=[]
    def source_case(name,old,new,diagnostic,group):
        require(source.count(old)==1, 'Nonunique source target: '+name)
        changed=source.replace(old,new,1)
        ast.parse(changed)
        cases.append((name,changed,fixture,diagnostic,group,'source'))
    def fixture_case(name,path,value,diagnostic,group='schema'):
        f=json.loads(fixture)
        target=f
        for key in path[:-1]:target=target[key]
        target[path[-1]]=value
        cases.append((name,source,json.dumps(f,indent=2)+'\n',diagnostic,group,'fixture'))
    source_case('wrong_even_terminal_velocity','endpoint = -1 if n % 2 == 0 else 0','endpoint = 0 if n % 2 == 0 else -1','WALK_COUNT','counts')
    source_case('extra_final_slack_area_test','if r <= m and area < int(strict):','if r <= m + 1 and area < int(strict):','WALK_COUNT','counts')
    source_case('integrate_previous_velocity','area = a + velocity','area = a + v','WALK_COUNT','counts')
    source_case('ordinary_strict_condition_dropped','(int(strict) if r < n else 0)','(0 if r < n else 0)','T_FIXTURE_COUNT','counts')
    source_case('wrong_divisor_sign','(-1) ** (k + d) * phi[k // d]','(-1) ** (k + d + 1) * phi[k // d]','EGZ_INTEGRAL_POSITIVE','counts')
    source_case('wrong_ordinary_convolution','T[k] * S[n-k] for k in range(1, n+1)','T[k] * S[n-k] for k in range(1, n)','S_STRONG_COMPONENT_RECURRENCE','counts')
    source_case('wrong_log_derivative_index','N[k] * S[n-k] for k in range(1, n+1)','N[k] * S[n-k] for k in range(1, n)','N_LOG_DERIVATIVE_RECURRENCE','counts')
    source_case('omit_self_convolution_empty_term','D[n-2*k] * S[k] for k in range(n//2+1)','D[n-2*k] * S[k] for k in range(1,n//2+1)','C_DS_CONVOLUTION','counts')
    source_case('strong_convolution_wrong_sign','D[n] == C[n] - sum(T[k]','D[n] == C[n] + sum(T[k]','D_C_ONE_MINUS_T','counts')
    source_case('gaussian_wrong_cross_term','mono(6, (0,0,-2,0))','mono(-6, (0,0,-2,0))','GAUSSIAN_COMPLETION','algebra')
    source_case('gaussian_wrong_marginal_power','F(-2)*2 + 3 == -1','F(-2)*2 + 2 == -1','GAUSSIAN_MARGINAL_TIME_POWER','algebra')
    source_case('empty_first_bridge_block','a,b=ell//2,ell-ell//2','a,b=0,ell','BRIDGE_SPLIT_BOUNDS','algebra')
    source_case('wrong_area_protection_height','H=delta/(4*eps)','H=delta/(2*eps)','BAD_EVENT_AREA_PROTECTION','algebra')
    source_case('wrong_endpoint_protection_height','H=delta/(4*eps)','H=delta/(8*eps)','BAD_EVENT_ENDPOINT_GUARD','algebra')
    source_case('inverse_amplitude_sign','h={\'L\':F(1),\'log_L\':beta,\'log_a\':F(-1)}','h={\'L\':F(1),\'log_L\':beta,\'log_a\':F(1)}','REFINED_INVERSE_CANCELLATION','algebra')
    source_case('wrong_machin_sign','pi_lo,pi_hi=16*a-4*d,16*b-4*c','pi_lo,pi_hi=16*a+4*d,16*b+4*c','MACHIN_PI_ENCLOSURE','certificates')
    source_case('wrong_lambda_normalization','F(N[k],k*4**k)','F(N[k],k*2**k)','PUBLISHED_LAMBDA_UPPER','certificates')
    source_case('omit_tail_lower_correction','tail_lo=(1-F(2,cutoff))/(3*sqrt_hi)','tail_lo=1/(3*sqrt_hi)','IMPORTED_TAIL_LOWER_FORMULA','certificates')
    source_case('wrong_tail_upper_scale','tail_hi=1/(3*sqrt_lo)','tail_hi=1/(2*sqrt_lo)','IMPORTED_TAIL_UPPER_FORMULA','certificates')
    source_case('exponential_positive_sign','term *= -value/j','term *= value/j','PUBLISHED_RATIO_UPPER','certificates')
    source_case('wrong_beta_integration_parameter','rising(F(9,4),j)/rising(F(4),j)','rising(F(9,4),j)/rising(F(3),j)','HYPERGEOMETRIC_COEFFICIENT','algebra')
    source_case('wrong_hypergeometric_argument','a2*=F(3,4)*(j+F(7,4))/(j+F(3,2))','a2*=F(1,2)*(j+F(7,4))/(j+F(3,2))','HYPERGEOMETRIC_COEFFICIENT','algebra')
    source_case('wrong_ceiling_direction','ceil(q0-eta)<=m<=ceil(q0+eta)','ceil(q0-eta)<m<ceil(q0+eta)','INVERSE_CEILING_BRACKETS','algebra')
    source_case('wrong_lambert_sign','t0=-a0*w0/gamma','t0=a0*w0/gamma','LAMBERT_SUBSTITUTION','algebra')
    fixture_case('wrong_C_fixture',['sequences','C',6],7,'C_FIXTURE_COUNT','counts')
    fixture_case('wrong_D_fixture',['sequences','D',6],4,'D_FIXTURE_COUNT','counts')
    fixture_case('wrong_N_fixture',['sequences','N',3],5,'N_FIXTURE_COUNT','counts')
    for name,key,value,code in [
        ('variance_one','variance',[1,1],'INCREMENT_VARIANCE'),
        ('lattice_span_two','span',[2,1],'SPAN_ONE'),
        ('missing_gaussian_half','gaussian_marginal_prefactor_square',[1,1],'GAUSSIAN_MARGINAL_FACTOR'),
        ('wrong_dominating_s_power','outer_s_power',[1,4],'OUTER_INTEGRABLE_POWER'),
        ('wrong_smoothing_alpha_power','smoothing_alpha_power',[-1,4],'SMOOTHING_ALPHA_POWER'),
        ('wrong_bad_epsilon_power','bad_epsilon_power',[3,2],'BAD_EVENT_EPSILON_POWER'),
        ('wrong_bad_delta_power','bad_delta_power',[-1,1],'BAD_EVENT_DELTA_POWER'),
        ('wrong_bad_n_power','bad_n_power',[-1,4],'BAD_EVENT_N_POWER'),
        ('missing_half_length_factor','half_length_power',[0,1],'HALF_LENGTH_FACTOR'),
        ('wrong_amplitude_variance_factor','amplitude_power_after_sigma',[-1,4],'AMPLITUDE_VARIANCE_FACTOR'),
        ('wrong_convolution_tail_power','convolution_far_power',[-1,2],'CONVOLUTION_FAR_POWER'),
        ('wrong_inverse_loglog_power','inverse_loglog_power',[1,4],'INVERSE_LOGLOG_POWER')]:
        fixture_case(name,['constants',key],value,code,'algebra')
    fixture_case('schema_changed_provenance_hash',['provenance','prior_results_sha256'],'0'*64,'SCHEMA_PRIOR_HASH')
    fixture_case('schema_boolean_integer',['sequences','C',0],True,'SCHEMA_INTEGER_TERM')
    fixture_case('schema_truncated_sequence',['sequences','N'],[0,1],'SCHEMA_SEQUENCE_LENGTH')
    fixture_case('schema_unknown_root_key',['unexpected'],0,'SCHEMA_ROOT_KEYS')
    fixture_case('schema_zero_denominator',['constants','variance'],[2,0],'SCHEMA_RATIONAL_TYPE')
    fixture_case('schema_unreduced_fraction',['constants','variance'],[4,2],'SCHEMA_RATIONAL_REDUCED')
    fixture_case('schema_float_fraction',['constants','variance'],[2.0,1],'SCHEMA_RATIONAL_TYPE')
    fixture_case('schema_wrong_range',['ranges','lambda_cutoff'],1668,'SCHEMA_RANGE_VALUE')
    fixture_case('schema_claims_numeric_amplitude',['limitations'],[], 'SCHEMA_LIMITATIONS')
    duplicate=fixture.replace('"schema_version": 1,','"schema_version": 1, "schema_version": 1,',1)
    require(duplicate!=fixture,'Duplicate-key mutation target absent')
    cases.append(('schema_duplicate_key',source,duplicate,'SCHEMA_DUPLICATE_KEY','schema','fixture'))
    clean=[]
    expected=(home/'results.json').read_text()
    with tempfile.TemporaryDirectory(prefix='report116-clean-checks-') as tmp:
        folder=Path(tmp)
        (folder/'validate.py').write_text(source)
        (folder/'fixtures.json').write_text(fixture)
        for optimized in [False,True]:
            run=execute(folder,optimized)
            require(run.returncode==0 and not run.stderr and run.stdout==expected,'Clean fresh-directory replay mismatch')
            clean.append({'optimized':optimized,'status':'PASS','result_sha256':digest(run.stdout.encode())})
    records=[]
    for name,mutant,mutated_fixture,diagnostic,group,kind in cases:
        runs=[]
        with tempfile.TemporaryDirectory(prefix='report116-mutant-') as tmp:
            folder=Path(tmp)
            (folder/'validate.py').write_text(mutant)
            (folder/'fixtures.json').write_text(mutated_fixture)
            for optimized in [False,True]:
                run=execute(folder,optimized,group)
                expected_prefix='VALIDATION_FAILURE '+diagnostic
                require(run.returncode==2 and run.stderr.startswith(expected_prefix) and not run.stdout,
                    name+' did not produce expected rejection '+expected_prefix+': '+repr((run.returncode,run.stdout,run.stderr)))
                runs.append({'optimized':optimized,'returncode':run.returncode,'diagnostic':run.stderr.strip()})
        records.append({'name':name,'kind':kind,'group':group,'expected_diagnostic':diagnostic,
            'validator_before_sha256':digest(source.encode()),'validator_after_sha256':digest(mutant.encode()),
            'fixture_before_sha256':digest(fixture.encode()),'fixture_after_sha256':digest(mutated_fixture.encode()),'runs':runs})
    after={name:digest((home/name).read_bytes()) for name in filenames}
    require(before==after,'Clean inputs changed during campaign')
    result={'status':'PASS','named_cases':len(records),'rejected_runs':2*len(records),
        'clean_fresh_directory_replay':clean,'clean_input_hashes_before':before,'clean_input_hashes_after':after,
        'clean_inputs_unchanged':True,'optimization_disabled_asserts':0,'mutations':records,
        'scope':'Expected-diagnostic mutation tests and fresh-directory byte replay test implementation sensitivity and reproducibility; they do not prove the analytic limit theorems.'}
    rendered=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(rendered)
    print(rendered,end='')

if __name__=='__main__':
    try:
        main()
    except (CampaignError,OSError,ValueError,SyntaxError,subprocess.TimeoutExpired) as e:
        print('MUTATION_CAMPAIGN_FAILURE '+str(e),file=sys.stderr)
        sys.exit(2)
