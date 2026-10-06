#!/usr/bin/env python3
"""Selected adversarial tests, isolated in temporary copies, normal and -O.
Each semantic mutation is rehashed to pass integrity first. These checks show
that the mathematical/schema guards are active, not merely that hashes differ.
"""
from hashlib import sha256
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent

class TestError(Exception): pass

def require(ok,message):
    if not ok: raise TestError(message)

def snapshot(root):
    return {p.relative_to(root).as_posix():sha256(p.read_bytes()).hexdigest()
            for p in root.rglob('*') if p.is_file()}

def seal(root):
    files=sorted(p for p in root.iterdir() if p.name!='manifest.sha256')
    (root/'manifest.sha256').write_text(''.join(sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n' for p in files),encoding='ascii')

def edit_json(root,name,mutator):
    p=root/name; data=json.loads(p.read_text());mutator(data)
    p.write_text(json.dumps(data,indent=2)+'\n');seal(root)

def change(root,path,value,name='evidence.json'):
    def mutation(d):
        for k in path[:-1]: d=d[k]
        d[path[-1]]=value
    edit_json(root,name,mutation)

def case_covariance(root): change(root,['covariance',0,1],'-3')
def case_corrector(root):
    def mutation(d): d['corrector'][0][0]='1/13';d['corrector'][1][0]='-2/13'
    edit_json(root,'evidence.json',mutation)
def case_reverse(root):
    def mutation(d): d['reverse_corrector'][0][1]='-4/3';d['reverse_corrector'][1][1]='8/3'
    edit_json(root,'evidence.json',mutation)
def case_critical(root): change(root,['critical',0],'4')
def case_vector(root): change(root,['right_vector',0],'3')
def case_loop(root): change(root,['loops',0,'steps',2,1],2)
def case_seed(root): change(root,['dual_seed','end',1],4)
def case_measure(root): change(root,['initial_measure',0],'1/4')
def case_inverse(root): change(root,['inverse_coefficients',1],'2')
def case_irrationality(root): change(root,['twice_double_angle_cosine'],'1')
def case_canonical(root): change(root,['covariance',0,0],'14/6')
def case_boolean(root): change(root,['ranges','brute'],True)
def case_range(root): change(root,['ranges','brute'],8)
def case_extra_key(root): change(root,['dual_seed','unexpected'],0)
def case_provenance(root): change(root,['historical_recomputation','role'],'external source','provenance.json')
def case_duplicate(root):
    p=root/'evidence.json';s=p.read_text();s=s.replace('"schema":','"schema":"a279571-finite-exact-v1",\n  "schema":',1);p.write_text(s);seal(root)
def case_table(root):
    p=root/'b279571.txt';s=p.read_text();require(s.startswith('0 1\n'),'TEST: b-file precondition');p.write_text('0 2\n'+s[4:]);seal(root)
def case_inventory(root): (root/'unlisted.txt').write_text('unexpected\n')
def case_hash(root):
    p=root/'evidence.json';p.write_text(p.read_text()+' ')

CASES=[
 ('covariance_cross_term',case_covariance,'COVARIANCE: Perron Hessian mismatch'),
 ('mean_zero_wrong_corrector',case_corrector,'CORRECTOR: Poisson equation'),
 ('wrong_reverse_corrector',case_reverse,'CORRECTOR: Poisson equation'),
 ('wrong_critical_point',case_critical,'TILT: characteristic root'),
 ('wrong_perron_vector',case_vector,'TILT: right eigenvector'),
 ('nonreturning_loop',case_loop,'LOOP: return mismatch'),
 ('wrong_dual_seed_endpoint',case_seed,'DUAL: seed endpoint'),
 ('wrong_initial_measure',case_measure,'RESOLVENT: first-step measure'),
 ('wrong_inverse_loglog_term',case_inverse,'INVERSE: logarithmic coefficient cancellation'),
 ('wrong_irrationality_premise',case_irrationality,'ARITHMETIC: twice double angle'),
 ('noncanonical_rational',case_canonical,'SCHEMA: covariance[0][0] canonical rational'),
 ('boolean_in_integer_field',case_boolean,'SCHEMA: ranges.brute integer'),
 ('weakened_range',case_range,'RANGE: mandatory coverage changed'),
 ('unknown_nested_key',case_extra_key,'SCHEMA: dual_seed keys'),
 ('historical_mislabeled_external',case_provenance,'PROVENANCE: historical role'),
 ('duplicate_json_key',case_duplicate,'JSON: duplicate key schema'),
 ('changed_external_coefficient',case_table,'TABLE: public source hash'),
 ('unlisted_payload',case_inventory,'INVENTORY: unexpected or missing member'),
 ('unresealed_payload',case_hash,'HASH: evidence.json'),
]

def run(root,optimized,output=None):
    args=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(root/'verify.py')]
    if output is not None:args+=['--output',str(output)]
    return subprocess.run(args,cwd=root.parent,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=180)

def main():
    require(len(sys.argv)==1 or (len(sys.argv)==3 and sys.argv[1]=='--output'),'USAGE: python3 negative_tests.py [--output PATH]')
    output=Path(sys.argv[2]).resolve() if len(sys.argv)==3 else None
    if output is not None: require(ROOT!=output and ROOT not in output.parents,'OUTPUT: path must be outside sealed checks directory')
    original=snapshot(ROOT);results=[]
    with tempfile.TemporaryDirectory(prefix='a279571-negative-') as temp:
        temp=Path(temp)
        for optimized in (False,True):
            tag='optimized' if optimized else 'normal'
            clean=temp/('clean-'+tag);shutil.copytree(ROOT,clean)
            before=snapshot(clean);target=temp/('result-'+tag+'.json')
            p=run(clean,optimized,target)
            require(p.returncode==0 and not p.stderr,'CLEAN REPLAY '+tag+': '+p.stderr)
            require(snapshot(clean)==before,'CLEAN REPLAY '+tag+': source modified')
            result=json.loads(target.read_text()); require(result['status']=='PASS','CLEAN REPLAY: missing PASS')
            results.append({'case':'clean_copy_replay','mode':tag,'status':'PASS','source_unchanged':True})
            for name,mutator,error in CASES:
                root=temp/(tag+'-'+name);shutil.copytree(ROOT,root);mutator(root)
                before=snapshot(root);p=run(root,optimized)
                require(p.returncode==1,'NEGATIVE '+tag+'/'+name+': expected exit 1, got '+str(p.returncode))
                require(p.stderr=='FAIL: '+error+'\n','NEGATIVE '+tag+'/'+name+': wrong diagnostic '+repr(p.stderr))
                require(p.stdout=='','NEGATIVE '+tag+'/'+name+': unexpected stdout')
                require(snapshot(root)==before,'NEGATIVE '+tag+'/'+name+': source modified')
                results.append({'case':name,'mode':tag,'status':'PASS','expected_diagnostic':'FAIL: '+error,'exit_status':1})
                shutil.rmtree(root)
    require(snapshot(ROOT)==original,'SOURCE: negative test modified original checks')
    result={'schema':'a279571-negative-results-v1','status':'PASS','negative_cases':len(CASES),'modes':['normal','optimized'],'negative_executions':2*len(CASES),'clean_copy_replays':2,'source_unchanged':True,'results':results}
    if output is not None:
        output.parent.mkdir(parents=True,exist_ok=True);output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print('PASS: '+str(len(CASES))+' selected negative cases in normal and -O modes ('+str(2*len(CASES))+' expected failures with exact diagnostics)')
    print('PASS: clean-copy replay normal and -O; all source inventories and bytes unchanged')
    return 0

if __name__=='__main__':
    try: sys.exit(main())
    except (TestError,OSError,ValueError,subprocess.TimeoutExpired) as exc:
        print('FAIL: '+str(exc),file=sys.stderr);sys.exit(1)
