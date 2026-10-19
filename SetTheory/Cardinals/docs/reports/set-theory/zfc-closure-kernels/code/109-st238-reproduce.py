#!/usr/bin/env python3
"""Portable exact construction and mathematical proof replay for M238.

The default runs both complete unbounded proofs. --quick omits them and
reports QUICK_238_REPLAY_PASS explicitly. All fresh outputs go to --output.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,time

ROOT=Path(__file__).resolve().parent

def require(ok,msg):
    if not ok:raise RuntimeError(msg)

def main():
    if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
        raise RuntimeError('Use Python with assertions enabled and PYTHONOPTIMIZE unset.')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--quick',action='store_true')
    ap.add_argument('--output',type=Path,default=Path('replay'));a=ap.parse_args()
    out=a.output.resolve();require(not out.exists() or not any(out.iterdir()),'Choose a new or empty output directory.')
    out.mkdir(parents=True,exist_ok=True)
    manifest=ROOT/'SHA256SUMS';require(manifest.is_file(),'Missing final SHA256SUMS manifest.')
    checked=0
    for line in manifest.read_text().splitlines():
        digest,name=line.split('  ',1);path=ROOT/name
        require(path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest()==digest,'Manifest mismatch: '+name);checked+=1
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
    records=[];started=time.monotonic()
    def job(name,script,args,receipt,status):
        print('Checking '+name,flush=True)
        command=[sys.executable,'-B',str(ROOT/script),*map(str,args)]
        with (out/(name+'.log')).open('w') as log:
            result=subprocess.run(command,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT)
        require(result.returncode==0,name+' failed; see '+str(out/(name+'.log')))
        value=json.loads(receipt.read_text());require(value.get('status')==status,name+' status is not a proof pass')
        records.append({'name':name,'status':status,'receipt':str(receipt.relative_to(out)),'script_sha256':hashlib.sha256((ROOT/script).read_bytes()).hexdigest()})
        return value
    built=out/'rebuilt'
    job('construction','build.py',['--out',built],built/'construction.json','PASS_EXACT_238_CONSTRUCTION')
    for name in ('zfc238.tm','zfc238_old.tm'):
        require((built/name).read_bytes()==(ROOT/'machines'/name).read_bytes(),'Rebuilt machine differs')
    job('source_identity','reference/source_interface/check_source_interface.py',
        ['--sites',ROOT/'sources/rotation240_sites.json','--blank-prefix',ROOT/'inputs/boundary239_startup.json','--output',out/'source_identity.json'],
        out/'source_identity.json','EXACT_LEAN_SOURCE_DATA_AND_SEED_IDENTITY_PASS')
    job('source_control','verification/verify_source_control.py',
        [ROOT/'sources/rotation240_sites.json',ROOT/'sources/boundary_sites.json','--output',out/'source_control.json'],
        out/'source_control.json','PASS_INDEPENDENT_SOURCE_CONTROL_EQUALITY')
    job('boundary_split','verification/verify_boundary_split.py',
        [ROOT/'inputs/repaired_boundary240_old.tm',ROOT/'inputs/boundary239_old.tm','--output',out/'boundary_split.json'],
        out/'boundary_split.json','PASS_INDEPENDENT_BOUNDARY_CONTEXT_SPLIT')
    job('local_fold','verification/verify_fold238.py',
        ['--old',ROOT/'inputs/boundary239_old.tm','--new',ROOT/'machines/zfc238_old.tm','--output-dir',out/'fold'],
        out/'fold/guarded_fold238_certificate.json','PASS_EXACT_GUARDED_POSITIVE_BLOCK_CERTIFICATE')
    job('open_tape','verification/check_open_tape238.py',
        ['--old',ROOT/'inputs/boundary239_old.tm','--new',ROOT/'machines/zfc238_old.tm','--output',out/'open_tape.json'],
        out/'open_tape.json','PASS_SYMBOLIC_OPEN_TAPE_POSITIVE_BLOCKS')
    job('bootstrap','verification/check_bootstrap.py',
        ['--old-labels',ROOT/'machines/zfc238_old.tm','--canonical',ROOT/'machines/zfc238.tm','--output',out/'bootstrap.json'],
        out/'bootstrap.json','PASS_EXACT_SPARSE_DENSE_CANONICAL_BOOTSTRAP')
    job('rejected_rotation','verification/check_rejected_rotation.py',
        ['--root',ROOT,'--output',out/'rejected_rotation.json'],out/'rejected_rotation.json',
        'PASS_REPRODUCED_REJECTED_ROTATION_COUNTEREXAMPLE')
    job('stack937','research/stack937/build.py',
        ['--reference',ROOT/'research/stack937/reference','--out',out/'stack937'],
        out/'stack937/verification.json','finite syntax and Boolean-clause audit; no TM state count')
    require((out/'stack937/stack937.bits').read_bytes()==(ROOT/'research/stack937/generated/stack937.bits').read_bytes(),'Regenerated stack packet differs')
    if not a.quick:
        runtime=job('unbounded_runtime238','verification/check_runtime.py',
            ['--table',ROOT/'machines/zfc238_old.tm','--sites',ROOT/'sources/boundary_sites.json','--states',238,'--output',out/'runtime238.json'],
            out/'runtime238.json','UNIVERSAL_MATHEMATICAL_PASS')
        require((runtime['cases'],runtime['symbolic_steps'],runtime['minimum_actual_steps'],len(runtime['directly_used_rows']))==(8386,2255513,13,476),'Wrong runtime census')
        guard=job('unbounded_boundary169','verification/certify_boundary169.py',
            ['--table',ROOT/'inputs/boundary239_old.tm','--sites',ROOT/'sources/boundary_sites.json','--output-dir',out/'guard'],
            out/'guard/guard169_universal.json','PASS_UNIVERSAL_RUNTIME_AND_EXACT_BOOT_GUARD')
        require((guard['cases'],guard['symbolic_rules'],guard['next_one_guard_visits'],guard['minimum_certified_one_run_length_constant'],guard['all_runtime_rows'])==(8386,2247513,32,23,478),'Wrong guard census')
    summary={'status':'QUICK_238_REPLAY_PASS' if a.quick else 'FULL_238_REPLAY_PASS','manifest_files_checked':checked,'unbounded_proofs_rerun':not a.quick,'jobs':records,'seconds':time.monotonic()-started,'python_version':sys.version,'canonical_sha256':hashlib.sha256((ROOT/'machines/zfc238.tm').read_bytes()).hexdigest(),'scope':'Ordinary executable mathematical certificates. Inherited logical source calibration is identified and cited; no new Lean/Rocq or serialized object-theory proof is executed.'}
    (out/'replay.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
