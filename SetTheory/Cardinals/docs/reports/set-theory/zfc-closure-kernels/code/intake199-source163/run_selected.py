#!/usr/bin/env python3
"""Four independently selected leaves on a fresh copy; no wrappers or manifests."""
import argparse, hashlib, json, os, shutil, signal, subprocess, sys, time
from pathlib import Path

sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(p):
    out={}
    for f in sorted(p.rglob('*')):
        assert not f.is_symlink(),f
        if f.is_file():out[str(f.relative_to(p))]={'sha256':sha(f),'bytes':f.stat().st_size}
    return out
def write(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--package',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    assert not a.output.exists();a.output.mkdir(parents=True)
    original=inventory(a.package);write(a.output/'original.json',original)
    work=a.output/'work';shutil.copytree(a.package,work);assert inventory(work)==original
    logs=a.output/'logs';logs.mkdir();outputs=a.output/'outputs';outputs.mkdir()
    jobs=[('source-blank',['code/audit.py','--root',str(work.resolve())],'evidence/source_blank.json',{'evidence/source_blank.json','machine/canonicalization.json'}),
          ('matrix',['code/theory/check_diagonal_matrix.py'],'code/theory/diagonal_matrix_check.json',{'code/theory/diagonal_matrix_check.json'}),
          ('pairing',['code/theory/check_dyadic_pairing.py'],'code/theory/dyadic_pairing_check.json',{'code/theory/dyadic_pairing_check.json'}),
          ('credit',['code/theory/protected_credit.py'],None,set())]
    actual={'status':'RUNNING','scope':'Four selected fresh finite leaves; no full primitive runtime or proof-assistant execution','package':str(a.package.resolve()),'runner_sha256':sha(Path(__file__)),'python':sys.executable,'jobs':[]}
    write(a.output/'actual.json',actual)
    for name,args,output,allowed in jobs:
        before=inventory(work);write(a.output/(name+'-before.json'),before)
        cmd=[sys.executable,'-B',*args];env=dict(os.environ,PYTHONOPTIMIZE='0',PYTHONDONTWRITEBYTECODE='1')
        start=time.monotonic();p=subprocess.Popen(cmd,cwd=work,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
        timed_out=False
        try:stdout,stderr=p.communicate(timeout=120)
        except subprocess.TimeoutExpired:
            timed_out=True;os.killpg(p.pid,signal.SIGKILL);stdout,stderr=p.communicate()
        elapsed=time.monotonic()-start
        (logs/(name+'.stdout')).write_bytes(stdout);(logs/(name+'.stderr')).write_bytes(stderr)
        after=inventory(work);write(a.output/(name+'-after.json'),after)
        changes={k:{'before':before.get(k),'after':after.get(k)}for k in sorted(set(before)|set(after))if before.get(k)!=after.get(k)}
        rec={'name':name,'argv':cmd,'cwd':str(work.resolve()),'timeout_seconds':120,'timed_out':timed_out,'returncode':p.returncode,'seconds':elapsed,'allowed_output_paths':sorted(allowed),'changes':changes,'input_capture_preserved':set(changes)<=allowed,'stdout_sha256':sha(logs/(name+'.stdout')),'stderr_sha256':sha(logs/(name+'.stderr'))}
        actual['jobs'].append(rec);write(a.output/'actual.json',actual)
        assert p.returncode==0 and not timed_out,rec
        assert set(changes)<=allowed,rec
        result=json.loads((work/output).read_text())if output else json.loads(stdout)
        write(outputs/(name+'.json'),result)
        if name=='source-blank':
            assert result['status']=='INDEPENDENT_FINITE_SOURCE_AND_COMPLETE_BLANK_PASS'
            assert(result['working_states'],result['rows'],result['guarded_edges'])==(216,432,6175)
            assert result['metrics']=={'leaf_occurrences':4751,'dag_nodes':203,'maximum_depth':48,'maximum_zero_run':6}
            assert [x['index']for x in result['source_changes']]==[973,978,1151,1156]
            s=result['startup'];assert(s['steps'],s['native_state'],s['head'],s['gap'],s['unit_spares'],s['one_cells'])==(313133,84,-5,80,130,277)
            assert s['logical_registers']==[3,0,0,0,3,0,0,0,0]and s['complete_zero_exterior']and s['changed_rows_absent']
            delivered=json.loads((a.package/'evidence/source_blank.json').read_text())
            assert{k:v for k,v in result.items()if k!='seconds'}=={k:v for k,v in delivered.items()if k!='seconds'}
            shutil.copy2(work/'machine/canonicalization.json',outputs/'canonicalization.json')
        elif name=='matrix':
            assert result['status']=='PASS'and sum(x['assignments']for x in result['schemata'].values())==207
            assert all(x['values']==[2]for x in result['schemata'].values())
            assert(result['modus_ponens_pairs'],result['generalization_pairs'])==(9,9)
            assert result==json.loads((a.package/'evidence/diagonal_matrix_check.json').read_text())
        elif name=='pairing':
            assert result['status']=='FINITE_SUPPORT_CHECK_PASS'
            assert[result[k]for k in['inverse_codes','pair_rectangular_cases','bidirectional_recoding_cases','constructor_intertwining_cases']]==[100000,640,512,1024]
            assert result==json.loads((a.package/'evidence/dyadic_pairing_check.json').read_text())
        else:
            assert result['status']=='FINITE_SUPPORT_CHECK_PASS'
            assert(result['explicit_words'],result['diagonals'],result['maximum_candidate_exclusive'])==(10000,2000,2001000)
            assert result==json.loads((a.package/'evidence/protected_credit_result.json').read_text())
        rec['semantic_gates']='PASS';rec['output_sha256']=sha(outputs/(name+'.json'));write(a.output/'actual.json',actual)
        print(name,'PASS',round(elapsed,3),flush=True)
    final=inventory(work);write(a.output/'final.json',final)
    assert inventory(a.package)==original
    actual.update(status='ALL_FOUR_SELECTED_LEAVES_PASS',original_unchanged=True,original_files=len(original),final_files=len(final))
    write(a.output/'actual.json',actual);print(actual['status'],flush=True)
if __name__=='__main__':main()
