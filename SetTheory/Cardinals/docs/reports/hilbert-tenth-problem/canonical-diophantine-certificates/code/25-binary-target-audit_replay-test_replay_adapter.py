#!/usr/bin/env python3
"""Fresh relocation and refusal tests for the binary-target audit path adapter."""
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
RUNNER=HERE/'replay_audits.py'


def check(ok,message):
    if not ok: raise RuntimeError(message)


def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def snapshot(root):
    result={}
    for p in [root,*sorted(root.rglob('*'))]:
        s=p.lstat()
        check(not stat.S_ISLNK(s.st_mode),'Original root unexpectedly contains symlink')
        check(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'Original root has nonregular object')
        result[str(p.relative_to(root))]=(s.st_mode,s.st_mtime_ns,s.st_size if p.is_file() else None,digest(p) if p.is_file() else None)
    return result


def invoke(runner,source,audit,output,options=('-I',),expected=None,env=None):
    p=subprocess.run([sys.executable,*options,str(runner),'--source-root',str(source),'--audit-root',str(audit),
        '--output',str(output)],capture_output=True,text=True,env=env)
    if expected is None:
        check(p.returncode==0,'Replay failed: '+p.stderr)
    else:
        check(p.returncode!=0,'Unsafe call unexpectedly passed')
        check(expected in p.stderr,'Unexpected refusal: '+p.stderr)
    return p


def main():
    check(sys.flags.optimize==0,'Run safety checks without optimization')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root',required=True)
    parser.add_argument('--audit-root',required=True)
    parser.add_argument('--output',required=True,help='New external results directory')
    a=parser.parse_args()
    roots=[]
    for raw in [a.source_root,a.audit_root,a.output]:
        check('..' not in Path(raw).parts,'Traversal rejected')
        p=Path(os.path.abspath(raw))
        check(not any(q.is_symlink() for q in [p,*p.parents]),'Symlink path rejected')
        roots.append(p)
    source,audit,destination=roots
    check(source.is_dir() and audit.is_dir(),'Input directories required')
    check(not destination.exists() and destination.parent.is_dir(),'Fresh output with existing parent required')
    for root in [source,audit,HERE]:
        check(not destination.is_relative_to(root) and not root.is_relative_to(destination),'Output overlap rejected')
    before=(snapshot(source),snapshot(audit)); tests=[]
    destination.mkdir(mode=0o700)
    with tempfile.TemporaryDirectory(prefix='binary-target-audit-replay-') as td:
        temp=Path(td)
        first=temp/'original-result'
        invoke(RUNNER,source,audit,first,options=('-I',))
        tests.append('isolated_original_frozen_replay')
        bundle=temp/'before-move'; bundle.mkdir()
        shutil.copytree(source,bundle/'science'); shutil.copytree(audit,bundle/'audit')
        (bundle/'tools').mkdir(); shutil.copy2(RUNNER,bundle/'tools/replay_audits.py')
        moved=temp/'moved-release'; bundle.rename(moved)
        second=temp/'moved-result'
        invoke(moved/'tools/replay_audits.py',moved/'science',moved/'audit',second,options=('-I',))
        for name in ['audit-receipt.json','audit-run.log','semantics-receipt.json','semantics-run.log','replay-receipt.json']:
            check((first/name).read_bytes()==(second/name).read_bytes(),'Relocation changed '+name)
        tests.append('moved_source_and_checkers_all_five_outputs_byte_identical')
        for option in ['-O','-OO']:
            out=temp/('rejected'+option)
            invoke(RUNNER,source,audit,out,options=(option,),expected='Optimized Python is forbidden')
            check(not out.exists(),'Optimized call created output'); tests.append('reject_'+option)
        env=dict(os.environ); env['PYTHONOPTIMIZE']='1'; out=temp/'env-optimized'
        invoke(RUNNER,source,audit,out,options=(),expected='Optimized Python is forbidden',env=env)
        check(not out.exists(),'Environment optimization created output'); tests.append('reject_PYTHONOPTIMIZE')
        out=temp/'nonisolated-result'; env=dict(os.environ); env.pop('PYTHONOPTIMIZE',None)
        invoke(RUNNER,source,audit,out,options=(),expected='Isolated Python is required',env=env)
        check(not out.exists(),'Nonisolated call created output'); tests.append('reject_nonisolated_python')
        existing=temp/'existing'; existing.mkdir()
        invoke(RUNNER,source,audit,existing,expected='Output already exists')
        check(not list(existing.iterdir()),'Existing output changed'); tests.append('reject_existing_output')
        for root,label in [(moved/'science','source'),(moved/'audit','audit'),(moved/'tools','adapter')]:
            out=root/'would-write'
            invoke(moved/'tools/replay_audits.py',moved/'science',moved/'audit',out,expected='Output must not overlap')
            check(not out.exists(),'Overlap created output'); tests.append('reject_output_inside_'+label)
        invoke(RUNNER,moved/'science',moved/'audit',moved,expected='Output must not overlap')
        tests.append('reject_output_containing_inputs')
        out=temp/'missing-parent/new-result'
        invoke(RUNNER,source,audit,out,expected='Output parent must already exist')
        check(not out.parent.exists(),'Missing parent was created'); tests.append('reject_missing_output_parent')
        out=str(temp)+'/made-up/../traversal-result'
        invoke(RUNNER,source,audit,out,expected='Parent traversal is forbidden')
        check(not (temp/'traversal-result').exists(),'Traversal created output'); tests.append('reject_literal_parent_traversal')
        target=temp/'symlink-target'; out=temp/'symlink-output'; out.symlink_to(target)
        invoke(RUNNER,source,audit,out,expected='Symlink path component rejected')
        check(not target.exists(),'Symlink target changed'); tests.append('reject_output_symlink')
        realparent=temp/'real-parent'; realparent.mkdir(); link=temp/'linked-parent'; link.symlink_to(realparent,target_is_directory=True)
        invoke(RUNNER,source,audit,link/'result',expected='Symlink path component rejected')
        check(not list(realparent.iterdir()),'Symlink ancestor changed'); tests.append('reject_output_symlink_ancestor')
        for root,label in [(moved/'science','source'),(moved/'audit','audit')]:
            link=temp/('linked-'+label); link.symlink_to(root,target_is_directory=True); out=temp/(label+'-link-result')
            invoke(RUNNER,link if label=='source' else source,link if label=='audit' else audit,out,expected='Symlink path component rejected')
            check(not out.exists(),'Symlink input created output'); tests.append('reject_'+label+'_root_symlink')
        for original,label in [(source,'source'),(audit,'audit')]:
            copied=temp/(label+'-internal-link'); shutil.copytree(original,copied)
            (copied/'unexpected-link').symlink_to(source/'ARCHITECTURE.md')
            out=temp/(label+'-internal-link-result')
            invoke(RUNNER,copied if label=='source' else source,copied if label=='audit' else audit,out,expected='Symlink input rejected')
            check(not out.exists(),'Internal symlink created output'); tests.append('reject_internal_'+label+'_symlink')
        copied=temp/'fifo-source'; shutil.copytree(source,copied); os.mkfifo(copied/'unexpected-pipe')
        out=temp/'fifo-result'
        invoke(RUNNER,copied,audit,out,expected='Nonregular input rejected')
        check(not out.exists(),'FIFO source created output'); tests.append('reject_nonregular_input')
        for original,label,filename in [(source,'source','ARCHITECTURE.md'),(audit,'checker','independent_check.py'),
                (audit,'semantic-checker','semantics_check.py'),(audit,'manifest','audit-manifest.json')]:
            copied=temp/('tampered-'+label); shutil.copytree(original,copied)
            with (copied/filename).open('ab') as stream: stream.write(b'\n')
            out=temp/(label+'-tamper-result')
            invoke(RUNNER,copied if label=='source' else source,copied if label!='source' else audit,out,
                expected='Frozen audit manifest hash mismatch' if label=='manifest' else 'Frozen input pin mismatch')
            check(not out.exists(),'Tampered input created output'); tests.append('reject_'+label+'_pin_mismatch')
        cache=moved/'audit/__pycache__'; cache.mkdir(exist_ok=True)
        (cache/'independent_check.cpython-999.pyc').write_bytes(b'not trusted executable bytes')
        third=temp/'cache-result'
        invoke(RUNNER,moved/'science',moved/'audit',third,options=('-I',))
        for name in ['audit-receipt.json','semantics-receipt.json','replay-receipt.json']:
            check((first/name).read_bytes()==(third/name).read_bytes(),'Cached bytes changed '+name)
        tests.append('unlisted_bytecode_cache_ignored_and_preserved')
        # Read-only relocated inputs exercise separation of reads and writes.
        protected=[moved/'science',moved/'audit']
        for root in protected:
            for p in sorted(root.rglob('*'),reverse=True): p.chmod(0o555 if p.is_dir() else 0o444)
            root.chmod(0o555)
        try:
            fourth=temp/'readonly-result'
            invoke(RUNNER,moved/'science',moved/'audit',fourth,options=('-I',))
            check((first/'replay-receipt.json').read_bytes()==(fourth/'replay-receipt.json').read_bytes(),'Read-only replay differs')
            tests.append('read_only_relocated_inputs_replay_unchanged')
        finally:
            for root in protected:
                root.chmod(0o755)
                for p in root.rglob('*'): p.chmod(0o755 if p.is_dir() else 0o644)
        check(before==(snapshot(source),snapshot(audit)),'Original bytes or metadata changed')
        tests.append('all_original_trees_bytes_modes_mtimes_preserved')
        for name in ['audit-receipt.json','audit-run.log','semantics-receipt.json','semantics-run.log','replay-receipt.json']:
            shutil.copyfile(first/name,destination/name)
        result={'status':'PASS','test_count':len(tests),'tests':tests,
            'main_receipt_sha256':digest(first/'audit-receipt.json'),'semantic_receipt_sha256':digest(first/'semantics-receipt.json'),
            'replay_receipt_sha256':digest(first/'replay-receipt.json'),'adapter_sha256':digest(RUNNER),
            'test_harness_sha256':digest(Path(__file__)), 'relocated_outputs_byte_identical':True,
            'original_inputs_preserved':True}
    (destination/'test-results.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))


if __name__=='__main__': main()
