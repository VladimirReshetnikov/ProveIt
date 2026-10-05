#!/usr/bin/env python3
"""Normal/-O replay and fail-closed intentional-corruption test suite."""
from __future__ import annotations
import ast,hashlib,json,platform,shutil,subprocess,sys,tempfile,time
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path(__file__).resolve().parent
RESULTS=ROOT/'results'
class SuiteError(RuntimeError):pass
def require(ok,label):
    if not ok:raise SuiteError(label)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def invoke(root,opt,section,out):
    cmd=[sys.executable]+(['-O'] if opt else [])+[str(root/'verify_exact.py'),'--section',section,'--output',str(out)]
    if out.exists():out.unlink()
    start=time.monotonic();run=subprocess.run(cmd,cwd=root,text=True,capture_output=True,check=False,timeout=180)
    require(out.is_file(),'verifier did not produce result JSON')
    data=json.loads(out.read_text())
    require(data.get('optimization')==int(opt),'interpreter mode mismatch')
    return run,data,round(time.monotonic()-start,6)
def refresh(root,name):
    path=root/'input_manifest.json';m=json.loads(path.read_text());m['files'][name]=sha(root/'inputs'/name);path.write_text(json.dumps(m,indent=2)+'\n')
def alter(root,name,fn):
    p=root/'inputs'/name;data=json.loads(p.read_text());fn(data);p.write_text(json.dumps(data,indent=2)+'\n');refresh(root,name)
def code(root,old,new):
    p=root/'verify_exact.py';s=p.read_text();require(s.count(old)==1,'nonunique corruption target');p.write_text(s.replace(old,new))
def profile(root,index,component,term):
    alter(root,'formal_coefficients.json',lambda z:z['f'][index].__setitem__(component,'('+z['f'][index][component]+')+('+term+')'))
def field(root,key,index):
    alter(root,'formal_coefficients.json',lambda z:z[key].__setitem__(index,'('+z[key][index]+')+1'))
def raw(root,insert):
    p=root/'inputs/formal_coefficients.json';p.write_text(p.read_text().replace('{','{'+insert,1));refresh(root,p.name)
def manifest_bool(root):
    p=root/'input_manifest.json';z=json.loads(p.read_text());z['schema']=True;p.write_text(json.dumps(z))
def hash_break(root):
    p=root/'inputs/formal_coefficients.json';p.write_text(p.read_text()+'\n')
def mutations():
    return [
      ('hash_mismatch','finite','input SHA-256 mismatch',hash_break),
      ('boolean_schema','finite','manifest version',manifest_bool),
      ('unknown_formal_field','finite','formal object schema',lambda root:alter(root,'formal_coefficients.json',lambda z:z.__setitem__('unexpected',0))),
      ('duplicate_key','finite','duplicate JSON key',lambda root:raw(root,'"sigma": [],')),
      ('nan_constant','finite','nonfinite JSON constant',lambda root:raw(root,'"unexpected": NaN,')),
      ('infinity_constant','finite','nonfinite JSON constant',lambda root:raw(root,'"unexpected": Infinity,')),
      ('unsafe_expression','finite','unsupported expression syntax',lambda root:alter(root,'formal_coefficients.json',lambda z:z['f'][0].__setitem__(0,"__import__('os')"))),
      ('truncated_profiles','finite','profile count',lambda root:alter(root,'formal_coefficients.json',lambda z:z['f'].pop())),
      ('truncated_scalar','finite','sigma count',lambda root:alter(root,'formal_coefficients.json',lambda z:z['sigma'].pop())),
      ('shortened_startup','finite','startup coverage configuration',lambda root:code(root,'STARTUP = 9','STARTUP = 8')),
      ('wrong_reference_count','finite','reference sequence',lambda root:alter(root,'reference_sequences.json',lambda z:z['values']['6'].__setitem__(6,z['values']['6'][6]+1))),
      ('broken_gram_identity','finite','positive Gram edge',lambda root:code(root,'A*Ap*F(z-1,z-d)','A*Ap*F(z,z-d)')),
      ('broken_symmetrizer','finite','symmetrizer factor identity',lambda root:code(root,'return first*second*F(z-r,z)*F(z-d,z-1)','return first*second*F(z-r,z)*F(z-d,z)')),
      ('false_obstruction','finite','naive gauge obstruction',lambda root:code(root,'naive_edge(d,n-1,1)>naive_edge(d,n,1)','naive_edge(d,n-1,1)<naive_edge(d,n,1)')),
      ('profile_boundary','formal','boundary profile',lambda root:profile(root,1,1,'1')),
      ('profile_derivative_gauge','formal','derivative gauge profile',lambda root:profile(root,1,0,'1')),
      ('profile_interior','formal','formal pair recurrence',lambda root:profile(root,1,0,'x**2')),
      ('highest_scalar','formal','formal pair recurrence',lambda root:field(root,'sigma',5)),
      ('wrong_carrier','endpoint','scalar carrier difference',lambda root:field(root,'carrier',1)),
      ('wrong_first_correction','endpoint','first endpoint coefficient',lambda root:field(root,'endpoint',0)),
      ('wrong_second_correction','endpoint','second endpoint coefficient',lambda root:field(root,'endpoint',1)),
      ('ternary_highest_scalar','ternary','ternary formal pair recurrence',lambda root:alter(root,'ternary_degree6.json',lambda z:z['sigma'].__setitem__(6,'('+z['sigma'][6]+')+1'))),
      ('ternary_carrier','ternary','ternary carrier difference',lambda root:alter(root,'ternary_degree6.json',lambda z:z['carrier'].__setitem__(2,'('+z['carrier'][2]+')+1'))),
      ('ternary_gamma_normalizer','ternary','ternary exact gamma normalizer',lambda root:alter(root,'ternary_degree6.json',lambda z:z.__setitem__('normalizer_log_n','0'))),
      ('ternary_cubic_log','ternary','ternary logarithmic endpoint coefficient',lambda root:alter(root,'ternary_degree6.json',lambda z:z['log_endpoint_t'].__setitem__(2,'('+z['log_endpoint_t'][2]+')+1'))),
    ]
def main():
    RESULTS.mkdir(exist_ok=True)
    record={'schema':1,'status':'FAIL','python':platform.python_version(),'started_utc':datetime.now(timezone.utc).isoformat(),'baseline':[],'corruption_tests':[],
      'checker_sha256':sha(ROOT/'verify_exact.py'),'runner_sha256':sha(ROOT/'run_checks.py'),'manifest_sha256':sha(ROOT/'input_manifest.json')}
    start=time.monotonic()
    try:
        for name in ('verify_exact.py','run_checks.py'):
            tree=ast.parse((ROOT/name).read_text());require(not any(isinstance(z,ast.Assert) for z in ast.walk(tree)),'assert gate present in '+name)
        record['no_assert_statements']=True
        for opt in (False,True):
            mode='optimized' if opt else 'normal';run,data,seconds=invoke(ROOT,opt,'all',RESULTS/(mode+'.json'))
            (RESULTS/(mode+'.log')).write_text(run.stdout+run.stderr)
            require(run.returncode==0 and data['status']=='PASS','baseline failed '+mode+': '+run.stdout+run.stderr)
            require(set(data['checks'])=={'finite','formal','endpoint','ternary'},'missing baseline section')
            record['baseline'].append({'mode':mode,'status':'PASS','result':mode+'.json','seconds':seconds,'gates':data['gates']})
            print('PASS baseline '+mode,flush=True)
        for name,section,reason,mutate in mutations():
            for opt in (False,True):
                mode='optimized' if opt else 'normal'
                with tempfile.TemporaryDirectory(prefix='.corruption-',dir=ROOT) as directory:
                    root=Path(directory);shutil.copy2(ROOT/'verify_exact.py',root/'verify_exact.py');shutil.copy2(ROOT/'input_manifest.json',root/'input_manifest.json');shutil.copytree(ROOT/'inputs',root/'inputs')
                    mutate(root);run,data,seconds=invoke(root,opt,section,root/'result.json')
                    require(run.returncode!=0 and data.get('status')=='FAIL','accepted corruption '+name+' '+mode)
                    require(data.get('error_type')=='VerificationError','wrong exception '+name+': '+str(data))
                    require(reason in data.get('error',''),'wrong rejection reason '+name+': '+data.get('error',''))
                    record['corruption_tests'].append({'name':name,'mode':mode,'section':section,'status':'REJECTED','expected_error':reason,'observed_error':data['error'],'seconds':seconds})
                    print('PASS rejected '+name+' '+mode,flush=True)
        require(len(record['corruption_tests'])==2*len(mutations()),'corruption test coverage')
        require(record['checker_sha256']==sha(ROOT/'verify_exact.py') and record['runner_sha256']==sha(ROOT/'run_checks.py') and record['manifest_sha256']==sha(ROOT/'input_manifest.json'),'input or code changed during suite')
        record['status']='PASS'
    except Exception as error:
        record['error_type']=type(error).__name__;record['error']=str(error);print('FAIL '+str(error),file=sys.stderr)
    record['elapsed_seconds']=round(time.monotonic()-start,6)
    (RESULTS/'suite.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':record['status'],'baseline_runs':len(record['baseline']),'corruptions_rejected':len(record['corruption_tests']),'seconds':record['elapsed_seconds']}),flush=True)
    return 0 if record['status']=='PASS' else 1
if __name__=='__main__':sys.exit(main())
