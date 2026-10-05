#!/usr/bin/env python3
"""Run exact verification and intentional corruption tests in normal and -O Python."""
from __future__ import annotations
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import time

ROOT=Path(__file__).resolve().parent
RESULTS=ROOT/'results'

class SuiteError(RuntimeError): pass

def require(condition,label):
    if not condition: raise SuiteError(label)

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def invoke(root,optimized,section,output):
    command=[sys.executable]+(['-O'] if optimized else [])+[str(root/'verify_exact.py'),'--section',section,'--output',str(output)]
    start=time.monotonic()
    if output.exists(): output.unlink()
    result=subprocess.run(command,cwd=root,text=True,capture_output=True,check=False,timeout=300)
    require(output.is_file(),'checker did not produce result JSON')
    data=json.loads(output.read_text(encoding='utf-8'))
    require(data.get('optimization') == int(optimized),'requested interpreter mode not used')
    return result,data,round(time.monotonic()-start,6)

def rehash(root,name):
    path=root/'input_manifest.json'
    manifest=json.loads(path.read_text(encoding='utf-8'))
    manifest['files'][name]=sha(root/'inputs'/name)
    path.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')

def alter_json(root,name,mutator):
    path=root/'inputs'/name
    data=json.loads(path.read_text(encoding='utf-8'))
    mutator(data)
    path.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
    # Deliberately refresh the test copy's digest: test the algebra, not just its hash.
    rehash(root,name)

def mutate_code(root,old,new):
    path=root/'verify_exact.py'
    code=path.read_text(encoding='utf-8')
    require(code.count(old)==1,'mutation target is not unique')
    path.write_text(code.replace(old,new),encoding='utf-8')

def mutations():
    def profile(index,component,term):
        return lambda root:alter_json(root,'formal_9.json',lambda d:d['f'][index].__setitem__(component,'('+d['f'][index][component]+')+('+term+')'))
    def field(key,index):
        return lambda root:alter_json(root,'endpoint_9.json',lambda d:d[key].__setitem__(index,'('+d[key][index]+')+1'))
    def provenance(root):
        with (root/'inputs'/'formal_9.json').open('a',encoding='utf-8') as handle:handle.write('\nintentional corruption\n')
    def endpoint(root):
        alter_json(root,'endpoint_9.json',lambda d:d.__setitem__('E','('+d['E']+')+t'))
    def sigma(root):
        alter_json(root,'formal_9.json',lambda d:d['sigma'].__setitem__(9,'('+d['sigma'][9]+')+1'))
    def duplicate(root):
        path=root/'inputs'/'formal_9.json'
        path.write_text(path.read_text(encoding='utf-8').replace('{','{"f": [],',1),encoding='utf-8')
        rehash(root,'formal_9.json')
    def invalid(root):
        alter_json(root,'formal_9.json',lambda d:d['f'][0].__setitem__(0,"__import__('os')"))
    def truncated(root):
        alter_json(root,'endpoint_9.json',lambda d:d['ratio'].pop())
    def empty(root):
        alter_json(root,'formal_9.json',lambda d:d.__setitem__('f',[]))
    def schema(root):
        path=root/'input_manifest.json'
        data=json.loads(path.read_text(encoding='utf-8'));data['schema']=True
        path.write_text(json.dumps(data),encoding='utf-8')
    def nonfinite(root,constant):
        path=root/'inputs'/'formal_9.json'
        path.write_text(path.read_text(encoding='utf-8').replace('{','{\"invalid\": '+constant+',',1),encoding='utf-8')
        rehash(root,'formal_9.json')
    return [
        ('input_hash','finite','input SHA-256 mismatch',provenance),
        ('boolean_schema','finite','manifest version',schema),
        ('nan_json','finite','nonfinite JSON constant',lambda root:nonfinite(root,'NaN')),
        ('infinity_json','finite','nonfinite JSON constant',lambda root:nonfinite(root,'Infinity')),
        ('empty_profiles','finite','profile count',empty),
        ('shortened_startup','finite','startup coverage configuration',lambda root:mutate_code(root,'STARTUP = 16','STARTUP = 15')),
        ('duplicate_json_key','finite','duplicate JSON key',duplicate),
        ('unsafe_expression','finite','unsupported expression syntax',invalid),
        ('truncated_coefficients','finite','endpoint count: ratio',truncated),
        ('profile_boundary','formal','boundary profile 1',profile(1,1,'1')),
        ('profile_gauge','formal','derivative gauge profile 1',profile(1,0,'1')),
        ('profile_grading','formal','P grading profile 1',profile(1,0,'x')),
        ('interior_profile','formal','formal pair recurrence',profile(1,0,'x**2')),
        ('highest_scalar','formal','formal pair recurrence',sigma),
        ('endpoint_taylor','endpoint','canonical endpoint Taylor series',endpoint),
        ('carrier_ell','endpoint','scalar carrier difference',field('ell',5)),
        ('log_correction','endpoint','endpoint logarithmic correction',field('log_correction',4)),
        ('multiplicative','endpoint','multiplicative correction',field('multiplicative',6)),
        ('ratio','endpoint','direct endpoint ratio coefficient',field('ratio',9)),
        ('lower_matrix_formula','finite','two-step',lambda root:mutate_code(root,
            'def lower(n,j): return F((3*n+j+1)*(3*n+j-1),9*(n+j)*(n+j-1))',
            'def lower(n,j): return F((3*n+j+1)*(3*n+j),9*(n+j)*(n+j-1))')),
        ('square_factor_formula','finite','C factor diagonal',lambda root:mutate_code(root,
            'def cdiag2(n,j): return F(3*n+j+1,3*(n+j))',
            'def cdiag2(n,j): return F(3*n+j+2,3*(n+j))')),
        ('symmetrizer_formula','finite','symmetrizer edge',lambda root:mutate_code(root,
            '9**j*rising(n,j)*rising(n+1,j)*rising(3*n+1,j)',
            '10**j*rising(n,j)*rising(n+1,j)*rising(3*n+1,j)')),
    ]

def main():
    RESULTS.mkdir(exist_ok=True)
    suite={'schema':1,'status':'FAIL','started_utc':datetime.now(timezone.utc).isoformat(),
           'python':platform.python_version(),'baseline':[],'corruption_tests':[],
           'checker_sha256':sha(ROOT/'verify_exact.py'),'runner_sha256':sha(ROOT/'run_checks.py'),
           'input_manifest_sha256':sha(ROOT/'input_manifest.json')}
    start=time.monotonic()
    try:
        for filename in ['verify_exact.py','run_checks.py']:
            tree=ast.parse((ROOT/filename).read_text(encoding='utf-8'))
            require(not any(isinstance(node,ast.Assert) for node in ast.walk(tree)),filename+' contains disabled-under-O assert gates')
        suite['no_assert_statements']=True
        for optimized in [False,True]:
            mode='optimized' if optimized else 'normal'
            result,data,elapsed=invoke(ROOT,optimized,'all',RESULTS/(mode+'.json'))
            (RESULTS/(mode+'.log')).write_text(result.stdout+result.stderr,encoding='utf-8')
            require(result.returncode==0 and data['status']=='PASS','baseline '+mode+' failed: '+result.stdout+result.stderr)
            require(set(data.get('checks',{}))=={'finite','symbolic','formal','endpoint'},'baseline missing a section')
            suite['baseline'].append({'mode':mode,'status':'PASS','returncode':result.returncode,'seconds':elapsed,'result':mode+'.json'})
            print('PASS baseline '+mode,flush=True)
        for name,section,error_substring,mutator in mutations():
            for optimized in [False,True]:
                mode='optimized' if optimized else 'normal'
                with tempfile.TemporaryDirectory(prefix='.corruption-',dir=ROOT) as directory:
                    copy=Path(directory)
                    shutil.copy2(ROOT/'verify_exact.py',copy/'verify_exact.py')
                    shutil.copy2(ROOT/'input_manifest.json',copy/'input_manifest.json')
                    shutil.copytree(ROOT/'inputs',copy/'inputs')
                    mutator(copy)
                    result,data,elapsed=invoke(copy,optimized,section,copy/'result.json')
                    require(result.returncode!=0 and data.get('status')=='FAIL',name+' accepted corruption under '+mode)
                    require(data.get('error_type')=='VerificationError',name+' failed for an unexpected error type')
                    require(error_substring in data.get('error',''),name+' failed for wrong reason: '+data.get('error',''))
                    suite['corruption_tests'].append({'name':name,'mode':mode,'section':section,
                        'status':'REJECTED','returncode':result.returncode,'seconds':elapsed,
                        'expected_error':error_substring,'observed_error':data['error']})
                    print('PASS rejected '+name+' '+mode,flush=True)
        require(len(suite['corruption_tests'])==2*len(mutations()),'missing corruption tests')
        # Refuse to record success if the primary files changed during this run.
        require(suite['checker_sha256']==sha(ROOT/'verify_exact.py'),'checker changed during suite')
        require(suite['runner_sha256']==sha(ROOT/'run_checks.py'),'runner changed during suite')
        require(suite['input_manifest_sha256']==sha(ROOT/'input_manifest.json'),'manifest changed during suite')
        suite['status']='PASS'
    except Exception as error:
        suite['error_type']=type(error).__name__
        suite['error']=str(error)
        print('FAIL '+str(error),file=sys.stderr,flush=True)
    suite['elapsed_seconds']=round(time.monotonic()-start,6)
    (RESULTS/'suite.json').write_text(json.dumps(suite,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'status':suite['status'],'baseline_runs':len(suite['baseline']),
                      'corruptions_rejected':len(suite['corruption_tests']),'seconds':suite['elapsed_seconds']}),flush=True)
    return 0 if suite['status']=='PASS' else 1

if __name__=='__main__':sys.exit(main())
