#!/usr/bin/env python3
"""Check enclosing output guards in disposable external paths, without input changes.

Supported replay uses captured stdout, never any frozen checker's --output.
The frozen author checker's direct external --output can overwrite files; this
historical behavior is preserved and is not the release's output contract.
"""
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent


def need(ok,message):
    if ok is not True:raise RuntimeError(message)


def snapshot():
    out={}
    for p in [ROOT]+sorted(ROOT.rglob('*')):
        s=p.lstat()
        need(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'Unsafe source path')
        out[p.relative_to(ROOT).as_posix()]=(hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None,stat.S_IMODE(s.st_mode),s.st_mtime_ns)
    return out


def invoke(script,args,optimized=False,env=None):
    return subprocess.run([sys.executable,'-I','-B']+(['-O'] if optimized else [])+[str(ROOT/script)]+args,capture_output=True,text=True,timeout=180,env=env)


def external_temp_parent():
    candidates=[os.environ[k] for k in ('TMPDIR','TEMP','TMP') if os.environ.get(k)]+['/tmp','/var/tmp']
    for value in candidates:
        p=Path(value).resolve()
        need(p!=ROOT and ROOT not in p.parents,'Temporary parent must be outside the release')
        if p.is_dir() and os.access(p,os.W_OK|os.X_OK):return p
    raise RuntimeError('No writable external temporary parent is available')


def main():
    before=snapshot()
    baseline=invoke('verify_release.py',['--verify-only'])
    need(baseline.returncode==0,'Baseline identity failed: '+baseline.stderr)
    stage=json.loads(baseline.stdout)['release_stage']
    rows=[]
    with tempfile.TemporaryDirectory(prefix='report39-output-guards-',dir=external_temp_parent()) as tmp:
        parent=Path(tmp)
        existing=parent/'existing';existing.mkdir();sentinel=existing/'sentinel';sentinel.write_bytes(b'preserve\n')
        file=parent/'existing-file';file.write_bytes(b'preserve file\n')
        alias=parent/'release-alias';alias.symlink_to(ROOT,target_is_directory=True)
        cases=[
          ('replay-in-release','verify_release.py',['--replay','--workdir',str(ROOT)],'Replay directory must be external',None),
          ('replay-in-evidence','verify_release.py',['--replay','--workdir',str(ROOT/'evidence')],'Replay directory must be external',None),
          ('receipt-in-release','verify_release.py',['--replay','--receipt-dir',str(ROOT/'new-receipts')],'Receipt directory must be external',None),
          ('receipt-symlink-alias','verify_release.py',['--replay','--receipt-dir',str(alias/'new-receipts')],'Receipt directory must be external',None),
          ('receipt-existing-directory','verify_release.py',['--replay','--receipt-dir',str(existing)],'Receipt directory must be new',None),
          ('receipt-existing-file','verify_release.py',['--replay','--receipt-dir',str(file)],'Receipt directory must be new',None),
          ('receipt-missing-parent','verify_release.py',['--replay','--receipt-dir',str(parent/'missing'/'receipts')],'Receipt directory parent must already exist',None),
          ('pdf-in-release','build_pdf.py',['--output',str(ROOT)],'PDF build directory must be external',None),
          ('pdf-in-evidence','build_pdf.py',['--output',str(ROOT/'evidence'/'new-build')],'PDF build directory must be external',None),
          ('pdf-existing-directory','build_pdf.py',['--output',str(existing)],'PDF build directory must be new or empty',None),
          ('pdf-existing-file','build_pdf.py',['--output',str(file)],'PDF build directory must be new or empty',None),
          ('jacobi-in-packet','jacobi/check_jacobi_addendum.py',['--output',str(ROOT/'jacobi'/'expected_jacobi_receipt.json')],'--output must be outside packet',None),
          ('jacobi-existing-file','jacobi/check_jacobi_addendum.py',['--output',str(file)],'--output must not overwrite an existing file',None),
          ('author-in-packet','evidence/check_unwrapped_family.py',['--output',str(ROOT/'evidence'/'expected_check_results.json')],'--output must be outside packet',None),
          ('independent-in-packet','evidence/independent/check_audit.py',['--output',str(ROOT/'evidence'/'independent'/'expected_audit_receipt.json')],'Output must be outside the packet',None),
          ('independent-existing-file','evidence/independent/check_audit.py',['--output',str(file)],'Output must be a new file',None),
          ('unsafe-temp-parent','verify_release.py',['--replay'],'Temporary parent must be outside the release',dict(os.environ,TMPDIR=str(ROOT))),
        ]
        if stage=='final':
            cases += [
             ('archive-in-release','archive_release.py',['--create',str(ROOT/'new.zip')],'Archive must be external',None),
             ('archive-existing-file','archive_release.py',['--create',str(file)],'Refusing to overwrite an existing archive',None)]
        for optimized in (False,True):
            for label,script,args,message,env in cases:
                result=invoke(script,args,optimized,env)
                need(result.returncode!=0 and message in result.stderr,'Wrong rejection: '+label+': '+result.stderr[-1500:])
                need(snapshot()==before,'Source changed on output-guard test: '+label)
                need(sentinel.read_bytes()==b'preserve\n' and file.read_bytes()==b'preserve file\n','Existing output changed')
                need(not (parent/'missing').exists(),'Missing output parent was created')
                rows.append({'case':label,'optimized':optimized,'rejected_without_source_or_existing_output_mutation':True})
    print(json.dumps({'schema':'report39-output-guard-regression-v1','status':'PASS','release_stage':stage,'cases':rows,'source_bytes_modes_mtimes_preserved':True,'frozen_author_external_output_overwrite_behavior':'preserved; excluded from supported replay','supported_replay_output':'captured stdout; optional external new receipt directory only'},indent=2,sort_keys=True))


if __name__=='__main__':main()
