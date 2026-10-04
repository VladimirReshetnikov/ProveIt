#!/usr/bin/env python3
"""Fresh finite safety/relocation tests for the independent audit's path adapter."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

HERE=Path(__file__).resolve().parent
RUNNER=HERE/'replay_independent_audit.py'


def check(ok,message):
    if not ok: raise RuntimeError(message)


def sha(data): return hashlib.sha256(data).hexdigest()
def snapshot(root):
    result={}
    for p in [root,*sorted(root.rglob('*'))]:
        s=p.lstat()
        check(not stat.S_ISLNK(s.st_mode),'Unexpected original symlink')
        result[str(p.relative_to(root))]=(s.st_mode,s.st_mtime_ns,sha(p.read_bytes()) if p.is_file() else None)
    return result


def run(runner,source,audit,output,option=None,expected=None,env=None):
    command=[sys.executable]+([option] if option else [])+[str(runner),'--source-root',str(source),
        '--audit-root',str(audit),'--output',str(output)]
    proc=subprocess.run(command,text=True,capture_output=True,env=env)
    if expected is None:
        check(proc.returncode==0,'Replay failed: '+proc.stderr)
    else:
        check(proc.returncode!=0,'Unsafe replay unexpectedly passed')
        check(expected in proc.stderr,'Wrong refusal: '+proc.stderr)
    return proc


def main():
    check(sys.flags.optimize==0,'Run the runner tests without optimized Python')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root',required=True)
    parser.add_argument('--audit-root',required=True)
    parser.add_argument('--output',required=True,help='Fresh external results directory')
    args=parser.parse_args()
    SOURCE=Path(os.path.abspath(args.source_root)); AUDIT=Path(os.path.abspath(args.audit_root))
    destination=Path(os.path.abspath(args.output))
    for p in [SOURCE,AUDIT,destination]:
        check('..' not in Path(str(p)).parts,'Parent traversal rejected')
        check(not any(q.is_symlink() for q in [p,*p.parents]),'Symlink path rejected')
    check(not destination.exists() and destination.parent.is_dir(),'Fresh output with existing parent required')
    for root in [SOURCE,AUDIT,HERE]:
        check(not destination.is_relative_to(root) and not root.is_relative_to(destination),'Output overlap rejected')
    destination.mkdir(mode=0o700)
    before=(snapshot(SOURCE),snapshot(AUDIT))
    tests=[]
    with tempfile.TemporaryDirectory(prefix='sandpile-audit-replay-test-') as td:
        temp=Path(td)
        first=temp/'first-result'
        run(RUNNER,SOURCE,AUDIT,first)
        tests.append('original_frozen_inputs_replay')
        bundle=temp/'before-move'; bundle.mkdir()
        shutil.copytree(SOURCE,bundle/'science')
        shutil.copytree(AUDIT,bundle/'audit')
        (bundle/'tools').mkdir(); shutil.copy2(RUNNER,bundle/'tools/replay.py')
        moved=temp/'after-move'; bundle.rename(moved)
        second=temp/'relocated-result'
        run(moved/'tools/replay.py',moved/'science',moved/'audit',second)
        for name in ['audit-receipt.json','audit-run.log','replay-receipt.json']:
            check((first/name).read_bytes()==(second/name).read_bytes(),'Relocation changed '+name)
        tests.append('moved_release_receipts_and_log_byte_identical')
        for opt in ['-O','-OO']:
            out=temp/('rejected'+opt)
            run(RUNNER,SOURCE,AUDIT,out,option=opt,expected='Optimized Python is forbidden')
            check(not out.exists(),'Optimized run created output')
            tests.append('reject_'+opt)
        env=dict(os.environ); env['PYTHONOPTIMIZE']='1'
        out=temp/'environment-optimized'
        run(RUNNER,SOURCE,AUDIT,out,expected='Optimized Python is forbidden',env=env)
        check(not out.exists(),'Environment-optimized run created output')
        tests.append('reject_PYTHONOPTIMIZE')
        existing=temp/'existing'; existing.mkdir()
        run(RUNNER,SOURCE,AUDIT,existing,expected='Output already exists')
        check(not list(existing.iterdir()),'Existing output was changed')
        tests.append('reject_existing_output')
        out=moved/'science/evidence/would-overlap'
        run(RUNNER,moved/'science',moved/'audit',out,expected='Output must not overlap')
        check(not out.exists(),'Overlapping output was created')
        tests.append('reject_output_inside_source')
        run(RUNNER,moved/'science',moved/'audit',moved,expected='Output must not overlap')
        tests.append('reject_output_containing_source')
        out=temp/'symlink-output'; target=temp/'symlink-output-target'
        out.symlink_to(target)
        run(RUNNER,SOURCE,AUDIT,out,expected='Symlink path component rejected')
        check(not target.exists(),'Symlink target was changed')
        tests.append('reject_output_symlink')
        target=temp/'real-parent'; target.mkdir()
        link=temp/'linked-parent'; link.symlink_to(target,target_is_directory=True)
        run(RUNNER,SOURCE,AUDIT,link/'new-result',expected='Symlink path component rejected')
        check(not list(target.iterdir()),'Symlink-parent target was changed')
        tests.append('reject_output_symlink_ancestor')
        link=temp/'linked-science'; link.symlink_to(moved/'science',target_is_directory=True)
        out=temp/'source-link-result'
        run(RUNNER,link,moved/'audit',out,expected='Symlink path component rejected')
        check(not out.exists(),'Symlink-source run created output')
        tests.append('reject_source_root_symlink')
        bad_source=temp/'source-with-link'; shutil.copytree(SOURCE,bad_source)
        (bad_source/'unexpected-link').symlink_to(AUDIT/'AUDIT.md')
        out=temp/'internal-link-result'
        run(RUNNER,bad_source,AUDIT,out,expected='Symlink input rejected')
        check(not out.exists(),'Internal-symlink run created output')
        tests.append('reject_internal_source_symlink')
        bad_source=temp/'tampered-source'; shutil.copytree(SOURCE,bad_source)
        with (bad_source/'PROOF.md').open('ab') as f: f.write(b'\n')
        out=temp/'tampered-source-result'
        run(RUNNER,bad_source,AUDIT,out,expected='Frozen input pin mismatch')
        check(not out.exists(),'Tampered-source run created output')
        tests.append('reject_scientific_pin_mismatch')
        bad_audit=temp/'tampered-audit'; shutil.copytree(AUDIT,bad_audit)
        with (bad_audit/'independent_check.py').open('ab') as f: f.write(b'\n')
        out=temp/'tampered-audit-result'
        run(RUNNER,SOURCE,bad_audit,out,expected='Frozen input pin mismatch')
        check(not out.exists(),'Tampered-checker run created output')
        tests.append('reject_checker_pin_mismatch')
        # Cached bytecode is not trusted or read by the adapter.
        fake_cache=moved/'audit/__pycache__'; fake_cache.mkdir()
        (fake_cache/'independent_check.cpython-999.pyc').write_bytes(b'not executable bytecode')
        third=temp/'ignored-cache-result'
        run(RUNNER,moved/'science',moved/'audit',third)
        check((first/'audit-receipt.json').read_bytes()==(third/'audit-receipt.json').read_bytes(),
            'Extraneous cached bytes changed replay')
        tests.append('ignore_unlisted_cached_bytecode')
        check(before==(snapshot(SOURCE),snapshot(AUDIT)),'Original source metadata or bytes changed')
        tests.append('all_original_bytes_modes_mtimes_trees_preserved')
        shutil.copyfile(first/'audit-receipt.json',destination/'replay-scientific-receipt.json')
        shutil.copyfile(first/'replay-receipt.json',destination/'replay-runner-receipt.json')
        result=dict(status='PASS',tests=tests,test_count=len(tests),
            scientific_receipt_sha256=sha((first/'audit-receipt.json').read_bytes()),
            replay_receipt_sha256=sha((first/'replay-receipt.json').read_bytes()),
            runner_sha256=sha(RUNNER.read_bytes()),test_harness_sha256=sha(Path(__file__).read_bytes()),
            relocated_scientific_receipt_equal=True,relocated_runner_receipt_equal=True,
            original_source_metadata_preserved=True)
    (destination/'test-results.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))


if __name__=='__main__': main()
