#!/usr/bin/env python3
"""Root-reviewed substantive leaf replay; retains every fresh output and log.

This deliberately does not run the delivered manifest-validation wrappers.
It does run all their mathematical verification jobs and compare their
substantive outputs. It makes no proof-assistant claim.
"""
from pathlib import Path
import concurrent.futures, hashlib, json, os, shutil, subprocess, sys, time

# Portable source/output selection only; the mathematical job runner below is unchanged.
import argparse
_ap = argparse.ArgumentParser(description=__doc__)
_ap.add_argument('--source-242', type=Path, required=True)
_ap.add_argument('--source-241', type=Path, required=True)
_ap.add_argument('--output', type=Path, required=True)
_args = _ap.parse_args()
OUT = _args.output.resolve()
SOURCES = {'242': _args.source_242.resolve(), '241': _args.source_241.resolve()}
if OUT.exists() or len(set(SOURCES.values())) != 2:
    raise ValueError('Output must be new and source roots distinct')
for _source in SOURCES.values():
    if not _source.is_dir() or _source == OUT or _source in OUT.parents or OUT in _source.parents:
        raise ValueError('Each source must exist and remain outside the new output tree')
def load(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
    result = {}
    for line in p.read_text().splitlines():
        if not line or line.startswith('#'): continue
        q,b,w,d,z = line.split()
        key = int(q),int(b)
        assert key not in result
        result[key] = int(w),d,int(z)
    return result
def main():
    assert __debug__ and not sys.flags.optimize and not OUT.exists()
    OUT.mkdir()
    (OUT / 'logs').mkdir()
    for name, source in SOURCES.items(): shutil.copytree(source, OUT / name)
    jobs = []
    def run(name, script, *args):
        suffix = '__' + hashlib.sha256(json.dumps(list(map(str,args))).encode()).hexdigest()[:12] if args else ''
        label = name + '__' + script.replace('/', '__') + suffix
        p = OUT / name / script
        stdout,stderr = OUT/'logs'/f'{label}.stdout.log',OUT/'logs'/f'{label}.stderr.log'
        command = [sys.executable,'-u','-B',str(p),*map(str,args)]
        start = time.monotonic()
        with stdout.open('w') as o,stderr.open('w') as e:
            cp = subprocess.run(command,cwd=p.parent,stdout=o,stderr=e,env={**os.environ,'PYTHONOPTIMIZE':'','PYTHONDONTWRITEBYTECODE':'1'})
        record = dict(name=name,script=script,command=command,returncode=cp.returncode,seconds=round(time.monotonic()-start,3),source_sha256=sha(p),stdout=str(stdout.relative_to(OUT)),stderr=str(stderr.relative_to(OUT)))
        (OUT/'logs'/f'{label}.json').write_text(json.dumps(record,indent=2)+'\n')
        assert cp.returncode == 0, record
        print(json.dumps(record),flush=True)
        return record
    local242 = ['root-proof/fold15_local_proof.py','local-proof/prove_local_folds.py','runtime/check_local_blocks_independent.py','runtime/check_boots.py','baseline243/independent-runtime/check_table_and_boot.py','baseline243/independent-runtime/check_local_compensation.py','baseline243/independent-runtime/check_source_rotation.py']
    # Independent local jobs have disjoint output files.
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
        jobs.extend(ex.map(lambda p:run('242',p),local242))
    for i in (1,2,3): jobs.append(run('242','runtime/crosscheck_instantiation.py',i))
    for script in ('root-proof/check.py','root-proof/boot.py','runtime/check_local_and_boot.py','runtime/crosscheck_instantiation.py'):
        jobs.append(run('241',script))
    a,b=OUT/'242',OUT/'241'
    assert (b/'runtime/baseline242_old.tm').read_bytes()==(a/'runtime/survivor_1_old.tm').read_bytes()
    assert (b/'runtime/sites_logical.json').read_bytes()==(a/'runtime/sites_logical.json').read_bytes()
    for name in ('independent_runtime.py','symbolic_runtime.py','run_symbolic_checked.py'):
        assert (b/'runtime'/name).read_bytes()==(a/'runtime'/name).read_bytes()==(a/'baseline243/independent-runtime'/name).read_bytes()
    for i,name in enumerate(('fold15_27','fold27_50','fold27_171'),1):
        assert table(a/f'runtime/survivor_{i}.tm')==table(a/f'local-proof/candidates/{name}/machine.tm')
        assert table(a/f'runtime/survivor_{i}_old.tm')==table(a/f'local-proof/candidates/{name}/machine_old.tm')
        boot=load(a/f'runtime/survivor_{i}_boot.json')
        assert boot['status']=='EXACT_WHOLE_BLANK_PASS' and boot['blank_transitions']==(407979,408291,407985)[i-1] and boot['ones']==351
        assert load(a/f'runtime/survivor_{i}_crosschecks.json')==load(SOURCES['242']/f'runtime/survivor_{i}_crosschecks.json')
    p=load(a/'root-proof/fold15_local_proof_result.json')
    assert p['finite_local_implications']==p['positive_block_checks']==7696
    assert load(a/'local-proof/local_proofs.json')['invariant_checks']==7640
    assert load(a/'runtime/local_blocks_independent.json')['status']=='ALL_THREE_INDEPENDENT_LOCAL_PROOFS_PASS'
    assert load(a/'baseline243/independent-runtime/source_rotation_and_composition.json')['status']=='UNIVERSAL_SOURCE_ROTATION_AND_FRAME_COMPOSITION_PASS'
    for name in ('candidate_1.tm','candidate_1_old.tm','renumbering.json'):
        assert (b/'runtime'/name).read_bytes()==(SOURCES['241']/'runtime'/name).read_bytes()
    p=load(b/'root-proof/result.json');assert p['invariant_implications']==p['whole_tape_block_checks']==7712
    p=load(b/'runtime/local_proof.json');assert p['status']=='INDEPENDENT_MAPPED_ALL_TAPE_PASS' and p['positive_whole_tape_blocks']==7712
    p=load(b/'runtime/boot.json');assert p['status']=='INDEPENDENT_241_WHOLE_BLANK_PASS' and p['blank_steps']==408419 and p['ones']==351 and p['clock_formula_extra_steps']==440
    assert load(b/'runtime/crosschecks.json')==load(SOURCES['241']/'runtime/crosschecks.json')
    old,new=table(a/'baseline243/sources/candidate-combined243__zfc_combined243_old.tm'),table(b/'runtime/candidate_1_old.tm')
    direct={(15,0):(0,'L',32),(17,0):(0,'L',106),(17,1):(1,'L',37),(18,0):(0,'L',15),(46,0):(0,'R',17),(47,0):(0,'L',15),(50,0):(0,'R',17),(65,0):(0,'L',15)}
    assert set(old)-set(new)=={(q,k) for q in (27,39) for k in (0,1)}
    assert {k:v for k,v in new.items() if old[k]!=v}==direct
    spec=load(b/'DIRECT_CONSTRUCTION.json')
    assert spec['deleted_inherited_states']==[27,39] and spec['retained_row_edits']==[dict(state=q,read=k,write=w,direction=d,target=z)for(q,k),(w,d,z)in sorted(direct.items())]
    tasks=[('242','runtime',f'survivor_{i}_old.tm','sites_logical.json',f'survivor_{i}_universal.json') for i in (1,2,3)]
    tasks += [('242','baseline243/independent-runtime','../sources/candidate-combined243__zfc_combined243_old.tm','../sources/candidate-combined243__sites_logical.json','combined243_universal.json'),('241','runtime','candidate_1_old.tm','sites_logical.json','candidate_1_universal.json')]
    def full(t):
        name,directory,tm,sites,output=t;d=OUT/name/directory
        job=run(name,directory+'/run_symbolic_checked.py','--table',d/tm,'--sites',d/sites,'--output',d/output)
        got,prior=load(d/output),load(SOURCES[name]/directory/output)
        assert got['status']=='UNIVERSAL_MATHEMATICAL_PASS' and got['cases']==got['expected_cases']==8390
        for k in ('table_sha256','sites_sha256','checker_sha256','helper_sha256','input_validation','symbolic_steps','minimum_actual_steps','blocks','directly_used_rows'):
            assert got[k]==prior[k],(t,k)
        cases=output.replace('.json','_cases.json')
        assert load(d/cases)==load(SOURCES[name]/directory/cases)
        return job,dict(name=name,table=tm,status=got['status'],cases=got['cases'],symbolic_steps=got['symbolic_steps'],minimum_duration=got['minimum_actual_steps'],rows=len(got['directly_used_rows']),all_case_outputs_match=True)
    universal=[]
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
        for job,receipt in ex.map(full,tasks): jobs.append(job);universal.append(receipt)
    result=dict(status='ROOT_SUBSTANTIVE_LEAF_REPLAY_PASS',arrival='8c41b1fb7d7bb8cd0612e37848181fe4a2f5d569',runner_sha256=sha(Path(__file__)),jobs=jobs,universal=universal,scope='All mathematical leaf jobs from both delivered verification suites freshly executed on persistent copies; case outputs compared. Manifest-validation wrappers not invoked. No new Lean or PA endpoint.')
    (OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
