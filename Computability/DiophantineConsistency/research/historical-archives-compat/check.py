#!/usr/bin/env python3
"""Exercise the exact wrapper bytes in an isolated Git repo sharing read-only objects."""
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
WRAPPER = ROOT / 'tools/with_historical_archives.py'


def need(ok, reason):
    if not ok:
        raise ValueError(reason)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pins=json.loads((HERE/'TOOL_PINS.json').read_bytes())
    need(pins['path']==str(WRAPPER.relative_to(REPO)) and pins['sha256']==sha256(WRAPPER.read_bytes()).hexdigest()
         and pins['bytes']==len(WRAPPER.read_bytes()) and pins['lines']==len(WRAPPER.read_bytes().splitlines())
         and pins['metadata_sha256']==sha256((HERE/'ARCHIVES.json').read_bytes()).hexdigest(), 'exact external tool/metadata bindings')
    manifest=HERE/'MANIFEST.json'
    if manifest.exists():
        files=json.loads(manifest.read_bytes())['files']
        need(set(files)=={str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p!=manifest}, 'closed compatibility packet inventory')
        for name,expected in files.items():
            need(sha256((HERE/name).read_bytes()).hexdigest()==expected,'sealed compatibility member '+name)
    frozen=HERE/'FROZEN_PINS.json'
    if frozen.exists():
        for name,record in json.loads(frozen.read_bytes())['files'].items():
            content=(REPO/name).read_bytes()
            need(len(content)==record['bytes'] and sha256(content).hexdigest()==record['sha256'], 'unchanged exact frozen replay input '+name)
    metadata = json.loads((HERE / 'ARCHIVES.json').read_bytes())
    objects = Path(subprocess.check_output(['git','rev-parse','--git-path','objects'],cwd=REPO,text=True).strip())
    if not objects.is_absolute():
        objects = (REPO / objects).resolve()
    controls = []
    with tempfile.TemporaryDirectory(prefix='historical-archives-controls-') as tmp:
        scratch = Path(tmp)
        subprocess.run(['git','init','-q',str(scratch)],check=True)
        (scratch/'.git/objects/info/alternates').write_text(str(objects)+'\n')
        local = scratch/'Computability/DiophantineConsistency'
        (local/'tools').mkdir(parents=True)
        (local/'research/historical-archives-compat').mkdir(parents=True)
        tool = local/'tools/with_historical_archives.py'
        tool.write_bytes(WRAPPER.read_bytes())
        (local/'research/historical-archives-compat/ARCHIVES.json').write_bytes((HERE/'ARCHIVES.json').read_bytes())
        archives = [scratch/r['path'] for r in metadata['archives']]
        first = archives[0]
        env = dict(os.environ)
        env.pop('CODEX_HISTORICAL_ARCHIVES_ACTIVE',None)
        prefix = [sys.executable,'-B']+(['-O'] if sys.flags.optimize else [])+[str(tool),'--']
        def run(code, *argv):
            return subprocess.run(prefix+[sys.executable,'-B','-c',code,*argv],cwd='/tmp',env=env,capture_output=True,text=True)
        def clean(except_paths=()):
            need({p for p in archives if os.path.lexists(p)}==set(except_paths),'exact historical-path cleanup set')
        def wait_for(path):
            deadline=time.monotonic()+12
            while not path.exists():
                need(time.monotonic()<deadline,'child-start rendezvous timed out')
                time.sleep(.02)
        code = ('import pathlib,sys; p=pathlib.Path.cwd(); '
                'count=len(list((p/"docs/incoming").glob("*.zip"))); '
                'print(count); print(p); print(sys.argv[1])')
        literal='$(touch SHOULD_NOT_EXIST); literal argument with spaces'
        result=run(code,literal)
        need(result.returncode==0 and result.stdout.splitlines()==['35',str(scratch),literal], 'argv/cwd/count forwarding')
        need(not (scratch/'SHOULD_NOT_EXIST').exists(),'no shell expansion')
        clean();need(not (scratch/'docs').exists(),'new empty archive parents cleaned by identity')
        controls.append('success_exact35_argv_repo_cwd_and_cleanup')
        result=run('raise SystemExit(23)')
        need(result.returncode==23,'exact failing-child status');clean();controls.append('failing_child_status_and_cleanup')
        result=subprocess.run(prefix+['/definitely/missing/historical-command'],env=env,capture_output=True,text=True)
        need(result.returncode==127,'missing command status');clean();controls.append('missing_command_cleanup')
        blob=subprocess.check_output(['git','cat-file','blob',metadata['archives'][0]['git_blob']],cwd=REPO)
        first.parent.mkdir(parents=True,exist_ok=True)
        first.write_bytes(blob)
        before=first.stat()
        result=run('pass')
        after=first.stat()
        need(result.returncode==0 and first.read_bytes()==blob and
             (before.st_dev,before.st_ino,before.st_mtime_ns)==(after.st_dev,after.st_ino,after.st_mtime_ns),
             'preexisting exact file identity/content/mtime preserved')
        clean([first]);first.unlink();controls.append('preexisting_exact_file_preserved')
        sentinel=b'preexisting archive integrity sentinel'
        first.write_bytes(sentinel);before=first.stat()
        marker=scratch/'unexpected-command'
        result=run('from pathlib import Path; Path(__import__("sys").argv[1]).write_text("bad")',str(marker))
        need(result.returncode==2 and first.read_bytes()==sentinel and first.stat().st_ino==before.st_ino and not marker.exists(),
             'mismatched preexisting archive refused without command or overwrite')
        clean([first]);first.unlink();controls.append('preexisting_mismatch_integrity_and_no_child')
        target=scratch/'symlink-sentinel';target.write_bytes(sentinel);first.symlink_to(target)
        result=run('pass')
        need(result.returncode==2 and first.is_symlink() and target.read_bytes()==sentinel,'preexisting symlink and target preserved')
        clean([first]);first.unlink();controls.append('preexisting_symlink_refused_and_preserved')
        result=run('from pathlib import Path; import sys; Path(sys.argv[1]).write_bytes(b"changed by child")',str(first))
        need(result.returncode==0 and first.read_bytes()==b'changed by child' and 'Preserved changed/replaced' in result.stderr,
             'changed owned file preserved with notice')
        clean([first]);first.unlink();controls.append('changed_created_file_preserved')
        result=run('from pathlib import Path; import sys,os; p=Path(sys.argv[1]); q=p.with_suffix(".replacement"); q.write_bytes(p.read_bytes()); os.replace(q,p)',str(first))
        need(result.returncode==0 and first.read_bytes()==blob and 'Preserved changed/replaced' in result.stderr,
             'identical-byte replacement inode preserved')
        clean([first]);first.unlink();controls.append('replaced_created_file_preserved')
        ready=scratch/'interrupt-ready'
        sleeper='from pathlib import Path; import sys,time; Path(sys.argv[1]).write_text("ready"); time.sleep(60)'
        process=subprocess.Popen(prefix+[sys.executable,'-B','-c',sleeper,str(ready)],env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        wait_for(ready);process.send_signal(signal.SIGTERM);out,err=process.communicate(timeout=12)
        need(process.returncode==143,'SIGTERM status');clean();controls.append('interrupt_child_termination_and_cleanup')
        ready1=scratch/'lock-first';release=scratch/'lock-release';ready2=scratch/'lock-second'
        holder='from pathlib import Path\nimport sys,time\nPath(sys.argv[1]).write_text("ready")\np=Path(sys.argv[2])\nwhile not p.exists(): time.sleep(.02)\n'
        first_process=subprocess.Popen(prefix+[sys.executable,'-B','-c',holder,str(ready1),str(release)],env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        wait_for(ready1)
        second_process=subprocess.Popen(prefix+[sys.executable,'-B','-c','from pathlib import Path; import sys; Path(sys.argv[1]).write_text("ready")',str(ready2)],env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
        time.sleep(.15)
        need(not ready2.exists() and second_process.poll() is None,'second wrapper waits on shared flock')
        release.write_text('release')
        first_process.communicate(timeout=12);second_process.communicate(timeout=12)
        need(first_process.returncode==second_process.returncode==0 and ready2.exists(),'serialized wrappers complete')
        clean();controls.append('concurrent_wrappers_serialized')
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),controls=controls,
                archive_count=35,archive_bytes=sum(r['bytes'] for r in metadata['archives']),
                wrapper_sha256=sha256(WRAPPER.read_bytes()).hexdigest(),metadata_sha256=sha256((HERE/'ARCHIVES.json').read_bytes()).hexdigest(),
                wrapper_bytes=len(WRAPPER.read_bytes()),wrapper_lines=len(WRAPPER.read_text().splitlines()),
                scratch_repo_uses_read_only_git_object_alternates=True,archive_code_executed=False,lean_run=False)
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    args.output.write_text(text);print(text,end='')


if __name__=='__main__':
    main()
