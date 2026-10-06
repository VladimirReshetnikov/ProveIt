#!/usr/bin/env python3
"""Selected independently authored rejection tests in sealed temporary copies."""
import sys
sys.dont_write_bytecode=True
from hashlib import sha256
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile

HOME=Path(__file__).resolve().parent
class BadTest(Exception):
    pass

def require(ok,message):
    if not ok:
        raise BadTest(message)

def snapshot(root):
    result={}
    for p in sorted(root.rglob('*')):
        name=p.relative_to(root).as_posix()
        if p.is_symlink():
            result[name]=['symlink',os.readlink(p)]
        elif p.is_dir():
            result[name]=['directory']
        elif p.is_file():
            result[name]=['file',sha256(p.read_bytes()).hexdigest()]
        else:
            result[name]=['nonregular',p.stat().st_mode]
    return result

def seal(root):
    files=sorted(p for p in root.iterdir() if p.name!='manifest.sha256')
    (root/'manifest.sha256').write_text(''.join(sha256(p.read_bytes()).hexdigest()+'  '+p.name+'\n' for p in files),encoding='ascii')

def field(path,value,filename='evidence.json'):
    def change(root):
        target=root/filename
        obj=json.loads(target.read_text())
        at=obj
        for key in path[:-1]:
            at=at[key]
        at[path[-1]]=value
        target.write_text(json.dumps(obj,sort_keys=True,indent=2)+'\n')
        seal(root)
    return change

def code(before,after):
    def change(root):
        target=root/'verify.py'
        text=target.read_text()
        require(text.count(before)==1,'MUTATION: source anchor must be unique')
        target.write_text(text.replace(before,after))
        seal(root)
    return change

def duplicate_json(root):
    f=root/'evidence.json'
    s=f.read_text()
    f.write_text(s.replace('"schema":','"schema":"duplicate",\n  "schema":',1))
    seal(root)

def nonfinite_json(root):
    f=root/'evidence.json'
    s=f.read_text()
    require(s.count('"row_height_max": 14')==1,'MUTATION: range anchor')
    f.write_text(s.replace('"row_height_max": 14','"row_height_max": NaN'))
    seal(root)

def unexpected(root):
    (root/'extra.txt').write_text('extra\n')

def directory(root):
    (root/'extra').mkdir()

def symlink(root):
    (root/'link').symlink_to('evidence.json')

def nonregular(root):
    target=root/'README.md'
    target.unlink()
    os.mkfifo(target)

def unsealed(root):
    f=root/'evidence.json'
    f.write_text(f.read_text()+' ')

def missing(root):
    (root/'README.md').unlink()

def missing_entry(root):
    f=root/'manifest.sha256'
    f.write_text('\n'.join(f.read_text().splitlines()[1:])+'\n')

def duplicate_entry(root):
    f=root/'manifest.sha256'
    f.write_text(f.read_text()+f.read_text().splitlines()[0]+'\n')

def malformed_entry(root):
    f=root/'manifest.sha256'
    f.write_text(f.read_text().replace('  ',' ',1))

def unsorted_entries(root):
    f=root/'manifest.sha256'
    f.write_text('\n'.join(reversed(f.read_text().splitlines()))+'\n')

CASES=[
 ('wrong_growth',field(['classes','759','mu'],8),'MODEL: 759'),
 ('wrong_terminal_extraction',field(['classes','247','terminal_cap'],None),'MODEL: 247'),
 ('wrong_ordinary_mass',field(['classes','247','a'],'1/3'),'MODEL: ordinary edge'),
 ('wrong_A0',field(['classes','247','A0'],'3/8'),'CRITICAL: A0'),
 ('nonzero_per_b_drift',field(['classes','759','R_derivatives','lambda'],'1'),'CRITICAL: 759 R lambda'),
 ('wrong_duration_mean',field(['classes','247','R_derivatives','eta'],'3/2'),'CRITICAL: 247 R eta'),
 ('wrong_variance',field(['classes','247','R_derivatives','lambda_lambda'],'1'),'CRITICAL: 247 R lambda_lambda'),
 ('erase_duration_covariance',field(['classes','759','R_derivatives','lambda_eta'],'0'),'CRITICAL: 759 R lambda_eta'),
 ('wrong_prefactor_shift',field(['classes','247','A_derivatives','lambda'],'0'),'CRITICAL: 247 A lambda'),
 ('wrong_diffusion',field(['classes','247','D'],'1'),'CRITICAL: diffusion'),
 ('wrong_killing',field(['classes','759','r'],'1'),'CRITICAL: row mass'),
 ('wrong_implicit_drift_sign',field(['algebra','drift_sign'],'1'),'DRIFT: implicit first derivative'),
 ('wrong_b0_clock_claim',field(['algebra','b0_duration'],'2'),'ROW: b0 duration'),
 ('cdf_cutoff_off_by_one',code('drop_cdf(kind,b,p-1,u)','drop_cdf(kind,b,p,u)'),'ROW: legal CDF equals raw drops'),
 ('negative_binomial_cdf_parameter',code('Q(b+1+k,k+1)*failure','Q(b+k,k+1)*failure'),'ROW: legal CDF equals raw drops'),
 ('binomial_cdf_parameter',code('Q(b+1-k,k+1)*success/(1-success)','Q(b-k,k+1)*success/(1-success)'),'ROW: legal CDF equals raw drops'),
 ('missing_bulk_duration_variance',code('variance_w = b*t/(1-t)**2','variance_w = Q(0)'),'MOMENT: raw law versus derivatives'),
 ('missing_clock_in_A',code('A = v/(9*(1-1/(3*u)))','A = 1/(9*(1-1/(3*u)))'),'CRITICAL: 759 A eta'),
 ('b0_has_spurious_bulk_step',code('return {0:1}','return {1:1}'),'DURATION: b0 first return'),
 ('count_last_fulfillment_twice',code('result[w] = result.get(w,0)+count','result[w] = result.get(w,0)+2*count'),'DURATION: Pascal first return'),
 ('renewal_duration_shortened',code('endtime = time+w+1','endtime = time+w'),'DURATION: 759 exact original-time recurrence'),
 ('renewal_endpoint_shift',code('endpoint = p-ell+w','endpoint = p-ell+w+1'),'DURATION: 759 exact original-time recurrence'),
 ('incorrect_internal_count',field(['classes','759','counts',8],3207),'DURATION: terminal prefix'),
 ('incorrect_certified_floor',field(['floor_samples',0,1],363665),'LOG: frozen floor anchors'),
 ('wrong_log_remainder_sign',code('return total,total+remainder','return total,total-remainder'),'LOG: certificate width'),
 ('wrong_repair_bridge_sign',field(['algebra','repair_bridge_sign'],'1'),'BRIDGE: exact repair'),
 ('wrong_stage_displacement',code('[(p,ell+gap,next_p),(next_p,ell-gap,p)]','[(p,ell+gap+1,next_p),(next_p,ell-gap,p)]'),'STAIRCASE: stage endpoint'),
 ('fill_excess_off_by_one',code('full,partial=divmod(excess,2*R)','full,partial=divmod(excess+1,2*R)'),'FILL: exact duration'),
 ('wrong_sharp_constant',field(['algebra','sigma_cube_pi2','759'],'3'),'CONSTANT: sigma cube'),
 ('wrong_derivative_saddle',field(['algebra','saddle_times_pi2','247'],'2'),'CONSTANT: derivative saddle'),
 ('wrong_inverse_scaling',field(['algebra','inverse_lambda_power'],'1/3'),'INVERSE: lambda scaling power'),
 ('wrong_derivative_loglog',field(['algebra','moment_loglog'],'2'),'DERIVATIVE: saddle coefficients'),
 ('wrong_formal_euler_sign',code('term(1,-2,0,1,Q(-1,2))','term(1,-2,0,1,Q(1,2))'),'FORMAL: Euler equation'),
 ('noncanonical_rational',field(['classes','759','y'],'2/4'),'SCHEMA: 759.y canonical rational'),
 ('boolean_range',field(['ranges','row_height_max'],True),'SCHEMA: ranges.row_height_max integer'),
 ('boolean_count',field(['classes','247','counts',0],True),'SCHEMA: count integer'),
 ('numeric_scope_boolean',field(['scope','finite_only'],1),'SCHEMA: scope boolean'),
 ('unknown_root_key',field(['extra'],1),'SCHEMA: evidence keys'),
 ('unknown_nested_key',field(['classes','759','R_derivatives','extra'],'1'),'SCHEMA: 759.R_derivatives keys'),
 ('weakened_range',field(['ranges','renewal_n_max'],21),'RANGE: mandatory coverage'),
 ('weakened_cutoff_coverage',field(['cutoffs'],[None,2,4]),'RANGE: boundary cutoffs'),
 ('duplicate_json_key',duplicate_json,'JSON: duplicate key schema'),
 ('nonfinite_json',nonfinite_json,'JSON: nonfinite number'),
 ('false_asymptotic_certificate',field(['scope','asymptotics_certified'],True),'SCOPE: finite analytic boundary'),
 ('false_fitted_digits',field(['scope','fitted_digits'],True),'SCOPE: finite analytic boundary'),
 ('false_fresh_retrieval',field(['fresh_network_retrieval'],True,'provenance.json'),'PROVENANCE: external data'),
 ('false_external_fixture',field(['external_sequence_fixtures'],['OEIS'],'provenance.json'),'PROVENANCE: external data'),
 ('wrong_proof_hash',field(['proof_sha256','sharp_upper'],'0'*64,'provenance.json'),'PROVENANCE: proof hashes'),
 ('wrong_primary_version',field(['source','version'],'arXiv:2512.21943v1','provenance.json'),'PROVENANCE: primary source'),
 ('unlisted_file',unexpected,'INVENTORY: closed members'),
 ('unlisted_directory',directory,'INVENTORY: directory'),
 ('symlink',symlink,'INVENTORY: symlink'),
 ('nonregular_member',nonregular,'INVENTORY: nonregular member'),
 ('unresealed_change',unsealed,'HASH: evidence.json'),
 ('missing_file',missing,'INVENTORY: closed members'),
 ('missing_manifest_entry',missing_entry,'MANIFEST: closed members'),
 ('duplicate_manifest_entry',duplicate_entry,'MANIFEST: duplicate'),
 ('malformed_manifest_entry',malformed_entry,'MANIFEST: syntax'),
 ('unsorted_manifest',unsorted_entries,'MANIFEST: sorted members'),
]

def run(root,optimized,path):
    command=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(root/'verify.py'),'--output',str(path)]
    env=os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE']='1'
    return subprocess.run(command,cwd=root.parent,capture_output=True,text=True,env=env,timeout=90)

def main():
    require(len(sys.argv)==1 or (len(sys.argv)==3 and sys.argv[1]=='--output'),'USAGE: negative_tests.py [--output PATH]')
    output=Path(sys.argv[2]).resolve() if len(sys.argv)==3 else None
    if output is not None:
        require(output!=HOME and HOME not in output.parents,'OUTPUT: outside sealed checks required')
    original=snapshot(HOME)
    completed=[]
    clean=[]
    with tempfile.TemporaryDirectory(prefix='report127-negative-') as name:
        temp=Path(name)
        for trial in range(2):
            for optimized in (False,True):
                root=temp/('clean-'+str(trial)+'-'+str(optimized))
                shutil.copytree(HOME,root)
                saved=snapshot(root)
                dest=temp/(root.name+'.json')
                process=run(root,optimized,dest)
                require(process.returncode==0 and process.stderr=='' and process.stdout=='PASS: Report127 independent finite exact checks\n','CLEAN: verifier failure '+process.stderr)
                require(snapshot(root)==saved,'CLEAN: source modified')
                clean.append(dest.read_bytes())
        require(all(x==clean[0] for x in clean),'CLEAN: normal optimized byte mismatch')
        for label,mutate,diagnostic in CASES:
            for optimized in (False,True):
                root=temp/(label+'-'+str(optimized))
                shutil.copytree(HOME,root)
                mutate(root)
                saved=snapshot(root)
                dest=temp/(root.name+'.json')
                process=run(root,optimized,dest)
                require(process.returncode==1,'NEGATIVE: '+label+' wrong exit '+str(process.returncode)+' '+process.stderr)
                require(process.stdout=='' and process.stderr=='FAIL: '+diagnostic+'\n','NEGATIVE: '+label+' wrong diagnostic '+repr(process.stderr))
                require(not dest.exists(),'NEGATIVE: rejected run wrote output')
                require(snapshot(root)==saved,'NEGATIVE: copy modified')
            completed.append({'case':label,'diagnostic':diagnostic,'normal':'PASS','optimized':'PASS'})
        for optimized in (False,True):
            root=temp/('output-'+str(optimized))
            shutil.copytree(HOME,root)
            saved=snapshot(root)
            process=run(root,optimized,root/'evidence.json')
            require(process.returncode==1 and process.stdout=='' and process.stderr=='FAIL: OUTPUT: outside sealed checks required\n','OUTPUT: refusal failed')
            require(snapshot(root)==saved,'OUTPUT: overwrote protected source')
    require(snapshot(HOME)==original,'IMMUTABILITY: original source modified')
    result={'schema':'report127-negative-results-v1','status':'PASS','selected_mutations':len(completed),'mutation_runs':2*len(completed),'modes':['normal','optimized'],'immutable_clean_copy_replays':4,'clean_results_byte_identical':True,'clean_result_sha256':sha256(clean[0]).hexdigest(),'output_refusal_runs':2,'all_source_inventories_unchanged':True,'cases':completed,'limitation':'Selected tests do not establish software correctness or any asymptotic theorem'}
    encoded=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if output is not None:
        output.write_text(encoded,encoding='utf-8')
    else:
        print(encoded,end='')
    if output is not None:
        print('PASS: '+str(len(completed))+' selected mutations in both modes; four immutable clean-copy replays')

if __name__=='__main__':
    try:
        main()
    except BadTest as exc:
        print('FAIL: '+str(exc),file=sys.stderr)
        sys.exit(1)
