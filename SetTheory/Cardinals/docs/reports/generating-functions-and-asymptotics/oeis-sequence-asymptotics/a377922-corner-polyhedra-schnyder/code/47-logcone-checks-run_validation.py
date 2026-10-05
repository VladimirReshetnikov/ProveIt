#!/usr/bin/env python3
"""Run ordinary and -O checks, adversarial fixtures, and a clean-directory replay.

Every mutant is valid JSON and syntactically valid input. A killed mutant must
exit 2 with its declared CheckFailure diagnostic, without a traceback. A crash,
syntax failure, timeout, or wrong diagnostic fails this validation runner.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
INPUTS=['validate.py','verify_sleeve.py','run_validation.py','fixtures.json','requirements.txt','README.md']

def sha(data):return hashlib.sha256(data).hexdigest()
def hashes(root):return {name:sha((root/name).read_bytes()) for name in INPUTS}

def require(condition,message):
    if not condition:raise RuntimeError(message)

def run(root,arguments):
    return subprocess.run([sys.executable,*arguments],cwd=root,capture_output=True,text=True,timeout=300)

def put(data,path,value):
    target=data
    for p in path[:-1]:target=target[p]
    target[path[-1]]=value

def remove(data,path):
    target=data
    for p in path[:-1]:target=target[p]
    del target[path[-1]]

def mutations():
    M='models';C='corner';S='schnyder'
    # name, category, path, replacement, required diagnostic
    specs=[
      ('corner_kernel_coefficient','mathematical',[M,C,'kernel',0,0,'numerator',0,0],'7','kernel.corner'),
      ('schnyder_kernel_coefficient','mathematical',[M,S,'kernel',0,0,'numerator',0,0],'7','kernel.schnyder'),
      ('corner_growth_constant','mathematical',[M,C,'gamma'],'5','normalization.corner.gamma'),
      ('schnyder_growth_constant','mathematical',[M,S,'gamma'],'5','normalization.schnyder.gamma'),
      ('corner_color_probability','mathematical',[M,C,'Q',0,0],'1/5','normalization.corner.Q'),
      ('schnyder_conditional_drift','mathematical',[M,S,'drift',0,0],'-1/3','drift.schnyder'),
      ('corner_poisson_corrector','mathematical',[M,C,'corrector',0,0],'-1/4','corrector.corner'),
      ('schnyder_poisson_corrector','mathematical',[M,S,'corrector',1,1],'-1/7','corrector.schnyder'),
      ('corner_phase_covariance','mathematical',[M,C,'phase_covariances',0,0,0],'4/5','phase_covariance.corner.0'),
      ('schnyder_phase_covariance','mathematical',[M,S,'phase_covariances',1,0,0],'3/2','phase_covariance.schnyder.1'),
      ('corner_effective_covariance','mathematical',[M,C,'covariance',0,0],'3/5','covariance.corner'),
      ('schnyder_effective_covariance','mathematical',[M,S,'covariance',0,1],'-1','covariance.schnyder'),
      ('corner_correlation','mathematical',[M,C,'rho'],'-1/2','correlation.corner'),
      ('schnyder_angle_cosine','mathematical',[M,S,'cos_angle'],'4/5','angle.schnyder.cosine'),
      ('corner_derivative_order','mathematical',[M,C,'derivative_order'],5,'angle.corner.derivative_order'),
      ('schnyder_derivative_order','mathematical',[M,S,'derivative_order'],5,'angle.schnyder.derivative_order'),
      ('corner_exponential_parameter','mathematical',[M,C,'moment_base'],'3','moment.corner.geometric_convergence'),
      ('schnyder_exponential_parameter','mathematical',[M,S,'moment_base'],'3/2','moment.schnyder.face_convergence'),
      ('corner_exponential_bound','mathematical',[M,C,'moment_bound'],'1','moment.corner.bound'),
      ('schnyder_exponential_bound','mathematical',[M,S,'moment_bound'],'1','moment.schnyder.bound'),
      ('corner_fourier_unsupported_edge','mathematical',[M,C,'fourier_edges',0,2],1,'fourier.corner.support'),
      ('corner_fourier_sublattice','mathematical',[M,C,'fourier_edges',1,3],3,'fourier.corner.unimodular'),
      ('schnyder_fourier_sublattice','mathematical',[M,S,'fourier_edges',1,2],-3,'fourier.schnyder.unimodular'),
      ('corner_forward_seed_endpoint','mathematical',[M,C,'seeds',0,'segments',0,'edges',0,'dy'],[1,0],'seed.corner.forward.endpoint_y'),
      ('corner_dual_seed_unsupported','mathematical',[M,C,'seeds',1,'segments',0,'edges',0,'dx'],[0,-1],'seed.corner.dual.support'),
      ('schnyder_forward_seed_boundary','mathematical',[M,S,'seeds',0,'segments',1,'repeat'],[0,1],'seed.schnyder.forward.quadrant'),
      ('schnyder_dual_seed_unsupported','mathematical',[M,S,'seeds',1,'segments',1,'edges',0,'dx'],[0,-1],'seed.schnyder.dual.support'),
      ('corner_endpoint_tilt','mathematical',['counting','corner_endpoint_factor'],'3','count.corner.endpoint_factor'),
      ('schnyder_endpoint_tilt','mathematical',['counting','schnyder_endpoint_factor'],'1','count.schnyder.endpoint_factor'),
      ('schnyder_aggregate_size_shift','mathematical',['counting','schnyder_aggregate_shift'],2,'count.schnyder.time_shift'),
      ('schnyder_original_time_shift','mathematical',['counting','schnyder_se_shift'],1,'count.schnyder.time_shift'),
      ('corner_size_sandwich','mathematical',['counting','corner_sandwich_shifts'],[-2,1],'count.corner.shifts'),
      ('schnyder_positive_transfer','mathematical',['counting','schnyder_positive_weights'],[1,3,1],'sequence.A377920'),
      ('a377922_recorded_term','mathematical',['sequences','A377922',9],123,'sequence.A377922'),
      ('a377920_recorded_term','mathematical',['sequences','A377920',10],973,'sequence.A377920'),
      ('a377921_recorded_term','mathematical',['sequences','A377921',8],43,'sequence.A377921'),
      ('a377921_convolution_weight','mathematical',['counting','a377921_weights'],[1,2,3,1],'count.A377921.convolution'),
      ('a377921_window_divisor','mathematical',['counting','a377921_window_divisor'],7,'count.A377921.window_divisor'),
      ('sleeve_old_edge_color','mathematical',['sleeve','old_boundary_edge_colors',0],'B','sleeve.local_SL2'),
      ('sleeve_radial_color','mathematical',['sleeve','radial_colors',0],'R','sleeve.local_SL2'),
      ('sleeve_outer_label','mathematical',['sleeve','new_boundary_labels',0],'R','sleeve.outer_SL1'),
      ('sleeve_canonical_order','mathematical',['sleeve','new_boundary_order',0],4,'sleeve.boundary_order'),
      ('sleeve_root_recovery','mathematical',['sleeve','recovered_old_root_position'],0,'sleeve.root_recovery'),
      ('sleeve_annulus_edge','mathematical',['sleeve','annulus_edges',12],[0,7],'sleeve.annulus_edges'),
      ('sleeve_face_boundary','mathematical',['sleeve','new_faces',0],[0,2,7,6],'sleeve.face_edges'),
      ('sleeve_euler_increment','mathematical',['sleeve','size_delta'],[6,12,5],'sleeve.euler_size'),
      ('sleeve_size_shift','mathematical',['sleeve','comparison_shift'],5,'sleeve.comparison_shift'),
      ('unknown_root_field','schema',['extra'],0,'schema.keys'),
      ('unknown_model_field','schema',[M,C,'extra'],0,'schema.keys'),
      ('noncanonical_rational','schema',[M,C,'gamma'],'18/4','schema.canonical_rational'),
      ('zero_denominator','schema',[M,C,'gamma'],'9/0','schema.rational'),
      ('boolean_as_integer','schema',[M,C,'derivative_order'],True,'schema.integer'),
      ('short_oeis_fixture','schema',['sequences','A377922'],[0,0,0,1],'schema.length'),
      ('integer_as_boolean','schema',['scope','symbolic_all_H_seeds'],1,'schema.boolean'),
      ('asymptotic_scope_overclaim','schema',['scope','asymptotic_certified'],True,'schema.scope'),
      ('missing_covariance','schema',[M,C,'covariance'],None,'schema.keys'),
      ('duplicate_json_key','schema',None,None,'schema.duplicate'),
    ]
    return specs

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay-child',action='store_true',help=argparse.SUPPRESS)
    parser.add_argument('--output',type=Path,default=HERE/'results')
    args=parser.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    before=hashes(HERE);fixture_bytes=(HERE/'fixtures.json').read_bytes();base=json.loads(fixture_bytes)
    report={'status':'PASS','hash_algorithm':'SHA-256','input_hashes_before':before,'runs':[],'mutations':[],'fresh_replay':None}
    for mode,prefix in [('ordinary',[]),('optimized',['-O'])]:
        result=run(HERE,[*prefix,'validate.py','--json',str(out/(mode+'.json'))])
        (out/(mode+'.log')).write_text(result.stdout+result.stderr)
        require(result.returncode==0 and 'PASS exact kernels' in result.stdout and not result.stderr,'Baseline '+mode+' failed: '+result.stdout+result.stderr)
        report['runs'].append({'mode':mode,'returncode':result.returncode,'summary':mode+'.json','log':mode+'.log'})
    with tempfile.TemporaryDirectory(prefix='cone-mutations-') as temporary:
        work=Path(temporary)
        for name,category,path,value,diagnostic in mutations():
            changed=copy.deepcopy(base)
            if name=='missing_covariance':remove(changed,path)
            elif name=='duplicate_json_key':pass
            else:put(changed,path,value)
            payload=(json.dumps(changed,indent=2)+'\n').encode()
            if name=='duplicate_json_key':payload=payload.replace(b'"schema_version": 1,',b'"schema_version": 1, "schema_version": 1,',1)
            mutant=work/(name+'.json');mutant.write_bytes(payload)
            result=run(HERE,['-O','validate.py','--fixtures',str(mutant)])
            stderr=result.stderr.strip()
            require(sha(payload)!=sha(fixture_bytes),'Mutation did not change fixture: '+name)
            require(result.returncode==2 and stderr.startswith('CHECK FAILED '+diagnostic) and 'Traceback' not in stderr and not result.stdout,
                    'Mutant '+name+' was not rejected as expected: '+repr((result.returncode,result.stdout,result.stderr)))
            report['mutations'].append({'name':name,'category':category,'mode':'python -O','expected_diagnostic':diagnostic,'actual_diagnostic':stderr,'returncode':result.returncode,'baseline_fixture_sha256':sha(fixture_bytes),'mutant_fixture_sha256':sha(payload),'status':'KILLED_BY_EXPECTED_CHECK'})
        if not args.replay_child:
            fresh=work/'fresh';fresh.mkdir()
            for filename in INPUTS:shutil.copy2(HERE/filename,fresh/filename)
            fresh_before=hashes(fresh)
            require(fresh_before==before,'Fresh replay bytes differ from source inputs')
            result=run(fresh,['run_validation.py','--replay-child'])
            require(result.returncode==0,'Fresh replay failed: '+result.stdout+result.stderr)
            child=json.loads((fresh/'results'/'validation_manifest.json').read_text())
            require(child['status']=='PASS' and child['input_hashes_before']==before and child['input_hashes_after']==before,'Fresh replay validation record mismatch')
            require(len(child['mutations'])==len(report['mutations']),'Fresh replay did not repeat every mutant')
            (out/'fresh_replay_manifest.json').write_text(json.dumps(child,indent=2)+'\n')
            (out/'fresh_replay.log').write_text(result.stdout+result.stderr)
            report['fresh_replay']={'status':'PASS','isolated_copy':True,'input_hashes_before':fresh_before,'input_hashes_after':hashes(fresh),'ordinary_and_optimized':True,'mutation_count':len(child['mutations']),'manifest':'fresh_replay_manifest.json','log':'fresh_replay.log'}
    after=hashes(HERE);require(before==after,'Baseline inputs changed during validation')
    report['input_hashes_after']=after
    report['mutation_count']=len(report['mutations'])
    report['mathematical_mutation_count']=sum(x['category']=='mathematical' for x in report['mutations'])
    report['schema_mutation_count']=sum(x['category']=='schema' for x in report['mutations'])
    (out/'validation_manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f"PASS ordinary and -O validation; {report['mutation_count']} named mutants rejected with expected diagnostics")
    print('PASS baseline SHA-256 inputs unchanged')
    if not args.replay_child:print('PASS fresh-directory standalone replay: both modes and all mutants repeated')
    print('Finite/algebraic certification only; no analytic asymptotic claim is certified')
    return 0

if __name__=='__main__':
    try:sys.exit(main())
    except (RuntimeError,subprocess.TimeoutExpired) as e:
        print('VALIDATION RUNNER FAILED: '+str(e),file=sys.stderr);sys.exit(1)
