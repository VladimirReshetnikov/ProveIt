#!/usr/bin/env python3
"""Pin package bytes, then replay explicitly owned finite checks in a disposable copy.
No downloaded code, proof assistant, upstream generator, or report build is run.
"""
import os,sys
if not __debug__ or sys.flags.optimize or 'PYTHONOPTIMIZE' in os.environ:
    raise SystemExit('UNSAFE_PYTHON_OPTIMIZATION: remove -O/-OO and unset PYTHONOPTIMIZE.')
import argparse,hashlib,json,shutil,subprocess,tempfile,time
from pathlib import Path,PurePosixPath
ROOT=Path(__file__).resolve().parent
MANIFEST_SHA256='efea1ad082184b255168f4df655f5492bda60ee4e801b84ec28c29f449a17756'
REPLAYS=[
 ('source_pins','check_source_pins.py',['SOURCE_PIN_CHECKS.json'],None),
 ('recorded_receipt_consistency','recent_commits/verify_receipts.py',['recent_commits/STATIC_AUDIT.json'],None),
 ('phase5_production_consistency','recent_commits/phase5_refresh/verify_phase5.py',['recent_commits/phase5_refresh/STATIC_AUDIT.json'],None),
 ('decoder_factoring','runtime_contexts/factor_decoder.py',['runtime_contexts/decoder_factored_certificate.json','runtime_contexts/decoder_factored_result.json'],None),
 ('home_profile','runtime_contexts/profile_home.py',['runtime_contexts/home_profile.json','runtime_contexts/home_cuts.json'],None),
 ('home_independent','runtime_contexts/verify_home.py',['runtime_contexts/home_independent_result.json'],None),
 ('optional_boundary','runtime_boundary_optional/check_boundary_optional.py',['runtime_boundary_optional/boundary_optional_result.json'],None),
 ('fresh_padding','calibration/check_fresh_padding.py',['calibration/finite_checks.json'],None),
 ('dag_wellformedness','wellformedness/check_wellformedness.py',['wellformedness/check_result.json','wellformedness/computed_summaries.json'],None),
 ('terminal_contract','terminal_contract/check_terminal_contract.py',[],'terminal_contract/result.json'),
 ('independent_review','review/check_independent.py',['review/independent_result.json'],None),
 ('named_kernel_review','review/check_named_kernel.py',['review/named_kernel_result.json'],None),
]
NEGATIVE_REPLAYS=[('runtime_rejections','runtime_contexts/test_rejections.py',['runtime_contexts/rejection_controls.json'],None),('outer_isolation','tests/test_outer_verifier.py',[],'OUTER_NEGATIVE_CONTROLS.json')]

def require(ok,message):
    if not ok:raise SystemExit(message)

def sha(data):return hashlib.sha256(data).hexdigest()

def inventory(root):
    result={}
    for p in root.rglob('*'):
        require(not p.is_symlink(),'SYMLINK_IN_RELEASE: '+str(p))
        if p.is_file():result[p.relative_to(root).as_posix()]=sha(p.read_bytes())
    return result

def validate_manifest():
    raw=(ROOT/'MANIFEST.json').read_bytes()
    require(sha(raw)==MANIFEST_SHA256,'MANIFEST_SHA256_MISMATCH')
    m=json.loads(raw)
    require(m['schema']=='further-proof-simplification-release-sha256-v1','MANIFEST_SCHEMA')
    require(isinstance(m['files'],dict),'MANIFEST_FILES')
    for name,pin in m['files'].items():
        rel=PurePosixPath(name)
        require(not rel.is_absolute() and '..'not in rel.parts and str(rel)==name,'UNSAFE_MANIFEST_PATH')
        p=ROOT.joinpath(*rel.parts)
        require(p.is_file() and not p.is_symlink(),'MISSING_OR_SYMLINK_FILE: '+name)
        require(ROOT in p.resolve().parents,'PATH_OUTSIDE_RELEASE: '+name)
        data=p.read_bytes()
        require(len(data)==pin['bytes'] and sha(data)==pin['sha256'],'PAYLOAD_SHA256_MISMATCH: '+name)
    require(set(inventory(ROOT))==set(m['files'])|{'MANIFEST.json','verify_release.py'},'UNMANIFESTED_OR_MISSING_FILE')
    return m

def compare_output(work,rel):
    original=(ROOT/rel).read_bytes();regenerated=(work/rel).read_bytes()
    require(original==regenerated,'REPLAY_OUTPUT_CHANGED: '+rel)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--hash-only',action='store_true')
    parser.add_argument('--negative-controls',action='store_true',help='Also run owned runtime rejection controls.')
    args=parser.parse_args();manifest=validate_manifest();before=inventory(ROOT)
    result={'status':'PASS_PACKAGE_INTEGRITY_ONLY'if args.hash_only else'PASS_FINITE_REPLAY_NOT_KERNEL_PROOF','manifest_sha256':MANIFEST_SHA256,'manifest_files':len(manifest['files']),'verifier_sha256':before['verify_release.py'],'python':sys.version.split()[0],'received_code_executed':False,'lean_or_rocq_compiled':False,'original_packet_unchanged':False,'checks':[]}
    if not args.hash_only:
        with tempfile.TemporaryDirectory(prefix='k215-further-replay-')as td:
            work=Path(td)/'packet';shutil.copytree(ROOT,work)
            env=dict(os.environ)
            for k in('PYTHONPATH','PYTHONHOME','PYTHONOPTIMIZE','PYTHONSTARTUP'):env.pop(k,None)
            env['PYTHONDONTWRITEBYTECODE']='1'
            for name,script,outputs,stdout_json in REPLAYS+(NEGATIVE_REPLAYS if args.negative_controls else[]):
                require(script in manifest['files'],'UNPINNED_CHECKER: '+script)
                started=time.monotonic()
                run=subprocess.run([sys.executable,'-I','-B',str(work/script)],cwd=work,env=env,capture_output=True,text=True,timeout=600)
                require(run.returncode==0,'REPLAY_FAILED: '+name+'\n'+run.stdout+'\n'+run.stderr)
                for output in outputs:compare_output(work,output)
                if stdout_json:require(json.loads(run.stdout)==json.loads((ROOT/stdout_json).read_text()),'STDOUT_RESULT_CHANGED: '+name)
                result['checks'].append({'name':name,'script':script,'exit_code':0,'archived_outputs_byte_equal':outputs,'stdout_json_equals':stdout_json,'stdout_sha256':sha(run.stdout.encode()),'stderr_sha256':sha(run.stderr.encode()),'python_replay_seconds_not_proof_assistant_benchmark':round(time.monotonic()-started,3)})
                print('PASS '+name,file=sys.stderr,flush=True)
    validate_manifest();require(before==inventory(ROOT),'ORIGINAL_RELEASE_CHANGED')
    result['original_packet_unchanged']=True
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
