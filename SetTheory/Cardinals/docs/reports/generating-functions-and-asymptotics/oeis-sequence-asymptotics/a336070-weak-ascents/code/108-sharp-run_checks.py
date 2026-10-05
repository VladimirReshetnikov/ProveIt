#!/usr/bin/env python3
"""Fail-closed corruption campaign; every mutation must fail at its named guard,
not merely at a generic hash. Baselines and mutations run both normally and -O.
All temporary mutation/replay directories are created within this checks tree.
"""
import argparse
import ast
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory
HERE=Path(__file__).resolve().parent
LOGS=HERE/'logs'

def require(condition,message):
    if not condition: raise RuntimeError(message)

def get(data,path):
    for part in path: data=data[part]
    return data

def put(data,path,value): get(data,path[:-1])[path[-1]]=value

def execute(script,fixture,expected,opt,name):
    command=[sys.executable]+(['-O'] if opt else [])+[str(script),'--fixtures',str(fixture),'--expected-summary',str(expected)]
    cp=subprocess.run(command,capture_output=True,text=True,timeout=120,cwd=str(script.parent))
    suffix='optimized' if opt else 'normal'
    LOGS.mkdir(exist_ok=True)
    (LOGS/(name+'.'+suffix+'.stdout')).write_text(cp.stdout)
    (LOGS/(name+'.'+suffix+'.stderr')).write_text(cp.stderr)
    payload=json.loads(cp.stdout if cp.returncode==0 else cp.stderr)
    return {'python_optimization':opt,'returncode':cp.returncode,'payload':payload,'stdout_log':'logs/'+name+'.'+suffix+'.stdout','stderr_log':'logs/'+name+'.'+suffix+'.stderr'}

def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('--skip-weak',action='store_true',help='Development only: do not rerun preserved weighted corruption campaign')
    args=parser.parse_args()
    original=(HERE/'fixtures.json').read_bytes(); source=(HERE/'verify_exact.py').read_text(); base=json.loads(original)
    for filename in ('verify_exact.py','weak_verify_exact.py'):
        require(not any(isinstance(n,ast.Assert) for n in ast.walk(ast.parse((HERE/filename).read_text()))),'assert correctness gate in '+filename)
    expected=HERE/'expected_summary.json'; records=[]; baselines=[]
    for opt in (0,1):
        result=execute(HERE/'verify_exact.py',HERE/'fixtures.json',expected,opt,'baseline')
        require(result['returncode']==0,'baseline failed'); baselines.append(result)
    si=next(i for i,c in enumerate(base['shifted_cases']) if c['M']==3 and c['r']=='1/2' and c['d']==2)
    zi=next(i for i,c in enumerate(base['shifted_cases']) if c['M']==3 and c['r']=='1' and c['d']==2)
    ci=next(i for i,c in enumerate(base['capped_cases']) if c['M']==3 and c['d']==2 and c['s']=='1/2' and c['v']=='17')
    xi=next(i for i,c in enumerate(base['crossing_cases']) if c['M']==3 and c['mode']=='increment_only')
    pi=next(i for i,c in enumerate(base['prefix_cases']) if c['d']==2 and c['k']==5)
    add=lambda x:str(F(x)+1)
    S=['shifted_cases',si,'rows',1]; Z=['shifted_cases',zi,'rows',1]; C=['capped_cases',ci]; X=['crossing_cases',xi]; P=['prefix_cases',pi]
    data_mutations=[
        ('shifted_normalizer',S+['normalizer'],add,'shifted_exact_algebra','shifted_normalizer_formula'),
        ('clipped_index',S+['l_prime'],lambda x:x+1,'shifted_exact_algebra','shift_clipped_index'),
        ('clipped_shift',S+['m'],lambda x:x+1,'shifted_exact_algebra','shift_clipped_index'),
        ('negative_shifted_probability',S+['P',0],lambda x:str(-F(x)),'shifted_exact_algebra','shifted_positive_stochastic'),
        ('positive_shifted_probability',S+['P',0],add,'shifted_exact_algebra','shifted_positive_stochastic'),
        ('shifted_poisson_value',S+['poisson_scaled'],add,'shifted_exact_algebra','shifted_poisson_fixture'),
        ('shifted_drift_value',S+['tracker_drift'],add,'shifted_exact_algebra','shifted_tracker_drift_fixture'),
        ('q0_shifted_probability',Z+['P',0],add,'shifted_exact_algebra','shifted_positive_stochastic'),
        ('capped_row_sum',C+['row_sums',1],add,'capped_exact_algebra','cap_finite_row_sum'),
        ('capped_bound',C+['bound'],add,'capped_exact_algebra','cap_bound_formula'),
        ('crossing_slope_drop',X+['slope_drop_exponents',1,1],add,'crossing_exact_algebra','crossing_slope_drop_fixture'),
        ('crossing_bound',X+['crossing_bound_exponent'],lambda x:x+1,'crossing_exact_algebra','crossing_bound_exponent'),
        ('crossing_q_order',X+['new_q_exponent'],lambda x:x+10000,'crossing_exact_algebra','crossing_exponent_domain'),
        ('difference_count',['recurrences',2,'counts',7],lambda x:x+1,'integer_recurrences','difference_incoming_recurrence'),
        ('d0_endpoint_count',['recurrences',0,'counts',7],lambda x:x+1,'integer_recurrences','difference_incoming_recurrence'),
        ('prefix_inversion_histogram',P+['inversion_words_by_r',0],lambda x:x+1,'exhaustive_prefixes','prefix_inversion_histogram'),
        ('prefix_legal_histogram',P+['legal_words_by_r',0],lambda x:x+1,'exhaustive_prefixes','prefix_legal_histogram'),
        ('prefix_stars_bars',P+['stars_bars',1],lambda x:x+1,'exhaustive_prefixes','prefix_stars_bars_formula'),
    ]
    source_mutations=[
        ('equation_shift_off_by_one','lp==max(l-(d-1),0)','lp==max(l-d,0)','shifted_exact_algebra','shift_clipped_index'),
        ('equation_normalizer_sign','norm==lam*r**(-m)','norm==lam*r**m','shifted_exact_algebra','shifted_normalizer_formula'),
        ('equation_tracker_shift_sign','rhs=1-F((j-lp)%M,M)+F(a*j,M*(M+a))+F(m,M)','rhs=1-F((j-lp)%M,M)+F(a*j,M*(M+a))-F(m,M)','shifted_exact_algebra','shifted_tracker_identity'),
        ('equation_poisson_sign','target=c+hc[lp]-hc[l]','target=c+hc[lp]+hc[l]','shifted_exact_algebra','shifted_poisson_cancellation'),
        ('equation_weak_row_index','prob[j]==p[(j-lp)%M]','prob[j]==p[(j-l)%M]','shifted_exact_algebra','shifted_weak_row_identity'),
        ('equation_q0_uniform','norm==M and prob==[F(1,M)]*M','norm==M+1 and prob==[F(1,M)]*M','shifted_exact_algebra','q0_shifted_uniform'),
        ('equation_q0_actual_zero','actual_b=actual_c=F(0)','actual_b=actual_c=F(1)','shifted_exact_algebra','q0_shifted_actual_zero'),
        ('equation_cap_geometric_sign','bound==(s**(-M)+v*s**(-h))/(1-s)','bound==(s**(-M)-v*s**(-h))/(1-s)','capped_exact_algebra','cap_bound_formula'),
        ('equation_cap_row_power','direct=sum((v if j>l-d else 1)*s**(j-l) for j in range(M))','direct=sum((v if j>l-d else 1)*s**(l-j) for j in range(M))','capped_exact_algebra','cap_finite_row_sum'),
        ('equation_crossing_denominator','slope=min(F(N,M+a),F(P))\n            for j','slope=min(F(N,M),F(P))\n            for j','crossing_exact_algebra','crossing_slope_drop_fixture'),
        ('equation_crossing_time_sign',"bound==P+L-N)","bound==P-L+N)",'crossing_exact_algebra','crossing_bound_exponent'),
        ('equation_recurrence_index','range(min(K,j+d))','range(min(K,j+d+1))','integer_recurrences','difference_incoming_recurrence'),
        ('equation_d0_endpoint',"values==base['zero_level']['fishburn'][:CN+1]","values==base['zero_level']['fishburn'][1:CN+2]",'integer_recurrences','d0_fishburn_endpoint'),
        ('equation_prefix_threshold','(y[i+1]>=y[i])==(x[i+1]>x[i]-d)','(y[i+1]>=y[i])==(x[i+1]>=x[i]-d)','exhaustive_prefixes','prefix_threshold_transform'),
        ('equation_prefix_inverse','decoded[i]-(d-1)*(i+1)','decoded[i]-d*(i+1)','exhaustive_prefixes','prefix_inverse_transform'),
        ('equation_stars_bars_index','formula=comb(D*(r+1)+k-1,k)','formula=comb(D*(r+1)+k,k)','exhaustive_prefixes','prefix_stars_bars_formula'),
    ]
    with TemporaryDirectory(prefix='mutation-',dir=HERE) as td:
        temp=Path(td)
        for name in ('weak_verify_exact.py','weak_fixtures.json','weak_expected_summary.json'):
            shutil.copy2(HERE/name,temp/name)
        def test(name,kind,script,fixture,phase,diagnostic,change):
            outcomes=[]
            for opt in (0,1):
                result=execute(script,fixture,expected,opt,name)
                require(result['returncode']!=0,name+': mutation survived')
                require(result['payload'].get('phase')==phase,name+': wrong phase '+str(result['payload']))
                require(diagnostic in result['payload'].get('error',''),name+': wrong guard '+str(result['payload']))
                outcomes.append(result)
            records.append({'name':name,'kind':kind,'change':change,'expected_phase':phase,'expected_diagnostic':diagnostic,'normal_and_optimized_detected':True,'results':outcomes})
        for name,path,mutation,phase,diagnostic in data_mutations:
            damaged=deepcopy(base); before=get(damaged,path); after=mutation(before); put(damaged,path,after)
            fixture=temp/(name+'.json'); fixture.write_text(json.dumps(damaged,indent=2)+'\n')
            test(name,'independent_fixture_mutation',HERE/'verify_exact.py',fixture,phase,diagnostic,{'json_path':path,'before':before,'after':after})
        for name,before,after,phase,diagnostic in source_mutations:
            require(source.count(before)==1,name+': nonunique anchor')
            script=temp/(name+'.py'); script.write_text(source.replace(before,after,1))
            test(name,'independent_equation_source_mutation',script,HERE/'fixtures.json',phase,diagnostic,{'before':before,'after':after})
        malformed=[
            ('missing_case',lambda:json.dumps({**base,'shifted_cases':base['shifted_cases'][:-1]}),'preflight','shifted_cases: complete inventory'),
            ('extra_top_key',lambda:json.dumps({**base,'unexpected':0}),'preflight','missing/extra keys'),
            ('duplicate_key',lambda:original.decode().replace('"schema":','"schema":"duplicate", "schema":',1),'preflight','duplicate JSON key'),
            ('float_inventory',lambda:original.decode().replace('"count_max_n": 16','"count_max_n": 16.0',1),'preflight','noninteger JSON number forbidden'),
            ('bool_inventory',lambda:original.decode().replace('"M": [\n      1,','"M": [\n      true,',1),'preflight','expected integer, not bool/float'),
            ('noncanonical_rational',lambda:original.decode().replace('"normalizer": "5"','"normalizer": "10/2"',1),'shifted_exact_algebra','noncanonical rational'),
            ('missing_nested_key',lambda:original.decode().replace('"normalizer": "5",','',1),'shifted_exact_algebra','missing/extra keys'),
        ]
        for name,make,phase,diagnostic in malformed:
            contents=make(); require(contents!=original.decode(),name+': unchanged malformed fixture')
            fixture=temp/(name+'.json'); fixture.write_text(contents)
            test(name,'independent_schema_mutation',HERE/'verify_exact.py',fixture,phase,diagnostic,{'operation':name})
    require((HERE/'fixtures.json').read_bytes()==original,'fixture changed during campaign')
    require((HERE/'verify_exact.py').read_text()==source,'verifier changed during campaign')
    for opt in (0,1):
        result=execute(HERE/'verify_exact.py',HERE/'fixtures.json',expected,opt,'final_baseline'); require(result['returncode']==0,'final baseline failed');baselines.append(result)
    if not args.skip_weak:
        weak=subprocess.run([sys.executable,str(HERE/'weak_run_checks.py')],cwd=HERE,capture_output=True,text=True,timeout=360)
        (HERE/'weak_campaign.stdout').write_text(weak.stdout); (HERE/'weak_campaign.stderr').write_text(weak.stderr)
        require(weak.returncode==0,'preserved weighted corruption campaign failed: '+weak.stderr)
    weak_result=json.loads((HERE/'weak_corruption_results.json').read_text()) if (HERE/'weak_corruption_results.json').exists() else None
    result={'schema':'report108-corruption-campaign-v1','status':'passed','scope':'Finite exact regression checks and deliberate mutation detection only; not analytic proof.','fixture_sha256':sha256(original).hexdigest(),'verifier_sha256':sha256(source.encode()).hexdigest(),'no_assertion_correctness_gates':True,'extension_independent_mutations':len(records),'extension_failed_corrupt_runs':2*len(records),'extension_baseline_successful_runs':len(baselines),'baseline':baselines,'mutations':records,'preserved_weighted_campaign':None if weak_result is None else {k:weak_result[k] for k in ('status','independent_mutations','failed_corrupt_runs','baseline_successful_runs')},'weak_campaign_rerun':not args.skip_weak}
    if weak_result is not None:
        result['combined_independent_mutations']=len(records)+weak_result['independent_mutations']; result['combined_failed_corrupt_runs']=2*len(records)+weak_result['failed_corrupt_runs']
    (HERE/'corruption_results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('baseline','mutations')},sort_keys=True))
    return 0
if __name__=='__main__':
    try: sys.exit(main())
    except Exception as error:
        print(json.dumps({'status':'failed','error_type':type(error).__name__,'error':str(error)},sort_keys=True),file=sys.stderr);sys.exit(1)
