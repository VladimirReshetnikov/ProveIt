#!/usr/bin/env python3
"""Selected mutations exercise active guards, including under python -O."""
import sys
sys.dont_write_bytecode=True
from hashlib import sha256
from pathlib import Path
import json
import shutil
import subprocess
import tempfile
ROOT=Path(__file__).resolve().parent
class TestError(Exception):pass
def require(ok,message):
    if not ok:raise TestError(message)
def snapshot(root):return {p.relative_to(root).as_posix():sha256(p.read_bytes()).hexdigest() for p in root.rglob('*') if p.is_file()}
def seal(root):
    files=sorted((p for p in root.rglob('*') if p.is_file() and p!=root/'manifest.sha256'),key=lambda p:p.relative_to(root).as_posix())
    (root/'manifest.sha256').write_text(''.join(sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(root).as_posix()+'\n' for p in files),encoding='ascii')
def change(root,path,value,name='evidence.json'):
    p=root/name;data=json.loads(p.read_text());part=data
    for k in path[:-1]:part=part[k]
    part[path[-1]]=value;p.write_text(json.dumps(data,indent=2)+'\n');seal(root)
def edit(path,value,name='evidence.json'):return lambda root:change(root,path,value,name)
def duplicate(root):
    p=root/'evidence.json';s=p.read_text();p.write_text(s.replace('"schema":','"schema":"a279571-leading-finite-v1",\n  "schema":',1));seal(root)
def nonfinite(root):
    p=root/'evidence.json';s=p.read_text();p.write_text(s.replace('"brute": 9','"brute": NaN',1));seal(root)
def extra(root):(root/'payload.txt').write_text('unlisted\n')
def extra_directory(root):(root/'empty').mkdir()
def symlink(root):(root/'alias').symlink_to('evidence.json')
def unsealed(root):
    p=root/'evidence.json';p.write_text(p.read_text()+' ')
def archive(root):
    p=root/'legacy/evidence.json';p.write_text(p.read_text()+' ');seal(root)
def archive_manifest(root):
    p=root/'legacy/manifest.sha256';p.write_text(p.read_text()+'\n');seal(root)
def missing_manifest_entry(root):
    p=root/'manifest.sha256';p.write_text('\n'.join(p.read_text().splitlines()[1:])+'\n')
def duplicate_manifest_entry(root):
    p=root/'manifest.sha256';s=p.read_text();p.write_text(s+s.splitlines()[0]+'\n')
CASES=[
 ('forward_drift',edit(['forward','drift',0,0],'1/15'),'CHAIN: forward drift'),
 ('forward_corrector',edit(['forward','h',0,0],'1/13'),'CHAIN: forward h'),
 ('dual_drift',edit(['dual','drift',0,0],'1/3'),'CHAIN: dual drift'),
 ('dual_corrector',edit(['dual','h',0,0],'1/2'),'CHAIN: dual h'),
 ('forward_conditional_covariance',edit(['forward','Gamma',0,0,1],'-3'),'CHAIN: forward Gamma'),
 ('dual_conditional_covariance',edit(['dual','Gamma',1,0,0],'2'),'CHAIN: dual Gamma'),
 ('forward_second_order_corrector',edit(['forward','B',0,0,0],'7/144'),'CHAIN: forward B'),
 ('dual_second_order_corrector',edit(['dual','B',0,1,1],'10/9'),'CHAIN: dual B'),
 ('effective_covariance',edit(['forward','Sigma',0,1],'-3'),'CHAIN: forward Sigma'),
 ('cycle_clock_endpoint_count',edit(['cycles','forward_P','mean',2],'1'),'CYCLE: forward_P original-clock mean'),
 ('cycle_time_cross_term',edit(['cycles','forward_P','covariance',0,2],'0'),'CYCLE: forward_P joint covariance'),
 ('dual_cycle_cross_sign',edit(['cycles','dual_P','covariance',0,2],'7/8'),'CYCLE: dual_P joint covariance'),
 ('Q_cycle_duration',edit(['cycles','forward_Q','mean',2],'2'),'CYCLE: forward_Q original-clock mean'),
 ('cycle_determinant',edit(['cycles','dual_Q','determinant'],'224'),'CYCLE: dual_Q joint determinant'),
 ('wrong_whitening',edit(['whitening','A',0,1,0],'-2/5'),'WHITENING: A Sigma A^T'),
 ('wrong_inverse_metric',edit(['whitening','inverse_sigma',0,1],'-2/5'),'WHITENING: metric inverse'),
 ('wrong_jacobian',edit(['whitening','determinant_squared'],'25/3'),'WHITENING: determinant squared'),
 ('wrong_angle',edit(['whitening','cosine_squared'],'3/7'),'WHITENING: wedge angle'),
 ('heatkernel_factor_two',edit(['brownian','b',0],'1'),'BROWNIAN: Bessel leading coefficient'),
 ('meander_integral',edit(['brownian','I1',0],'1'),'BROWNIAN: meander integral normalization'),
 ('midpoint_integral',edit(['brownian','I2',0],'1/2'),'BROWNIAN: midpoint integral normalization'),
 ('survival_constant',edit(['brownian','k',0],'2'),'BROWNIAN: survival coefficient'),
 ('reflection_constant',edit(['brownian','reflection_b_pi','3'],'1/4'),'BROWNIAN: special-angle b*pi p=3'),
 ('inverse_log_lambda_sign',edit(['inverse','center_coefficients',2],'1'),'INVERSE: complete constant centering cancellation'),
 ('inverse_log_amplitude_sign',edit(['inverse','center_coefficients',3],'1'),'INVERSE: complete constant centering cancellation'),
 ('inverse_defect_sign',edit(['inverse','defect_coefficient'],'1'),'INVERSE: exact log(1+b/L) defect sign'),
 ('inverse_envelope',edit(['inverse','envelope_factor'],'1'),'INVERSE: stated error envelope factor'),
 ('count_time_shift',edit(['counting','time_shift'],0),'COUNTING: original step shift'),
 ('count_leading_factor',edit(['counting','leading_factor'],'2'),'COUNTING: leading 2/9 factor'),
 ('terminal_color_factor',edit(['counting','terminal_stationary',0],'1/3'),'COUNTING: terminal stationary normalization'),
 ('noncanonical_rational',edit(['forward','Sigma',0,0],'14/6'),'SCHEMA: forward.Sigma[0][0] canonical rational'),
 ('boolean_as_integer',edit(['ranges','brute'],True),'SCHEMA: ranges.brute integer'),
 ('boolean_monomial_exponent',edit(['brownian','b',1],False),'SCHEMA: brownian.b exponent integer'),
 ('weakened_range',edit(['ranges','tree'],64),'RANGE: mandatory coverage changed'),
 ('unknown_nested_field',edit(['cycles','forward_P','extra'],'1'),'SCHEMA: cycles.forward_P keys'),
 ('duplicate_json_key',duplicate,'JSON: duplicate key schema'),
 ('nonfinite_json_number',nonfinite,'JSON: nonfinite number'),
 ('historical_falsely_fresh',edit(['public_fixture','fresh_gmp_run'],True,'provenance.json'),'PROVENANCE: public/historical distinction'),
 ('false_analytic_certificate',edit(['proof_source','role'],'finite proof certificate','provenance.json'),'PROVENANCE: analytic source boundary'),
 ('wrong_source_digest',edit(['proof_source','sha256'],'0'*64,'provenance.json'),'PROVENANCE: analytic source boundary'),
 ('changed_immutable_archive',archive,'ARCHIVE: immutable evidence.json'),
 ('changed_archive_manifest',archive_manifest,'ARCHIVE: Report123 manifest anchor'),
 ('unlisted_payload',extra,'INVENTORY: unexpected or missing member'),
 ('unlisted_empty_directory',extra_directory,'INVENTORY: unexpected or missing directory'),
 ('symlink_payload',symlink,'INVENTORY: symlink forbidden'),
 ('unresealed_payload',unsealed,'HASH: evidence.json'),
 ('missing_manifest_entry',missing_manifest_entry,'MANIFEST: closed inventory mismatch'),
 ('duplicate_manifest_entry',duplicate_manifest_entry,'MANIFEST: duplicate member'),
]
def run(root,optimized,output=None,script='verify.py',timeout=300):
    args=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(root/script)]
    if output is not None:args+=['--output',str(output)]
    return subprocess.run(args,cwd=root.parent,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=timeout)
def main():
    require(len(sys.argv)==1 or (len(sys.argv)==3 and sys.argv[1]=='--output'),'USAGE: python3 negative_tests.py [--output PATH]')
    output=Path(sys.argv[2]).resolve() if len(sys.argv)==3 else None
    if output is not None:require(output!=ROOT and ROOT not in output.parents,'OUTPUT: path must be outside sealed checks directory')
    original=snapshot(ROOT);results=[];clean_outputs=[]
    with tempfile.TemporaryDirectory(prefix='a279571-leading-negative-') as td:
        temp=Path(td)
        for optimized in (False,True):
            tag='optimized' if optimized else 'normal';clean=temp/('clean-'+tag);shutil.copytree(ROOT,clean)
            before=snapshot(clean);target=temp/('clean-'+tag+'.json');p=run(clean,optimized,target)
            require(p.returncode==0 and not p.stderr,'CLEAN '+tag+': '+p.stderr)
            require(snapshot(clean)==before,'CLEAN '+tag+': changed source bytes')
            require(json.loads(target.read_text())['status']=='PASS','CLEAN '+tag+': no PASS')
            clean_outputs.append(target.read_bytes());results.append({'case':'clean_copy_replay','mode':tag,'status':'PASS','source_unchanged':True})
            for name,mutation,error in CASES:
                copy=temp/(tag+'-'+name);shutil.copytree(ROOT,copy);mutation(copy);before=snapshot(copy)
                p=run(copy,optimized)
                require(p.returncode==1,'NEGATIVE '+tag+'/'+name+': expected exit 1, got '+str(p.returncode))
                require(p.stderr=='FAIL: '+error+'\n','NEGATIVE '+tag+'/'+name+': wrong diagnostic '+repr(p.stderr))
                require(not p.stdout,'NEGATIVE '+tag+'/'+name+': unexpected stdout')
                require(snapshot(copy)==before,'NEGATIVE '+tag+'/'+name+': changed source bytes')
                results.append({'case':name,'mode':tag,'status':'PASS','expected_diagnostic':'FAIL: '+error,'exit_status':1});shutil.rmtree(copy)
        require(clean_outputs[0]==clean_outputs[1],'CLEAN: normal/-O result bytes differ')
        # Replay archived semantic regressions in their own immutable companion.
        # It internally tests both normal and -O and reseals only private copies.
        archived=temp/'archived-negative.json';before=snapshot(ROOT)
        p=run(ROOT/'legacy',False,archived,'negative_tests.py',900)
        require(p.returncode==0 and not p.stderr,'ARCHIVE NEGATIVE: '+p.stderr)
        require(snapshot(ROOT)==before,'ARCHIVE NEGATIVE: source bytes changed')
        legacy=json.loads(archived.read_text());require(legacy['status']=='PASS','ARCHIVE NEGATIVE: no PASS')
    require(snapshot(ROOT)==original,'SOURCE: negative suite modified source')
    result={'schema':'a279571-leading-negative-results-v1','status':'PASS','leading_negative_cases':len(CASES),'leading_negative_executions':2*len(CASES),'legacy_negative_cases':legacy['negative_cases'],'legacy_negative_executions':legacy['negative_executions'],'total_selected_negative_cases':len(CASES)+legacy['negative_cases'],'total_negative_executions':2*len(CASES)+legacy['negative_executions'],'modes':['normal','optimized'],'clean_copy_replays':2+legacy['clean_copy_replays'],'normal_optimized_result_bytes_equal':True,'source_unchanged':True,'results':results,'legacy_results':legacy}
    if output is not None:output.parent.mkdir(parents=True,exist_ok=True);output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('PASS: '+str(len(CASES))+' leading and '+str(legacy['negative_cases'])+' archived selected negative cases, each in normal and -O modes')
    print('PASS: exact diagnostics, normal/-O result-byte identity, clean-copy replay and unchanged source inventories/bytes')
    return 0
if __name__=='__main__':
    try:sys.exit(main())
    except (TestError,OSError,ValueError,subprocess.TimeoutExpired) as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
