#!/usr/bin/env python3
"""Check external fresh output guards without changing the authenticated input.
Supported replay captures stdout and exports only to a fresh external directory.
Frozen source checker --output guards their scientific packet; direct use is
excluded from the enclosing release contract and checked only in disposable copies.
"""
import shutil
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
    with tempfile.TemporaryDirectory(prefix='report41-output-guards-',dir=external_temp_parent()) as tmp:
        parent=Path(tmp)
        existing=parent/'existing';existing.mkdir();sentinel=existing/'sentinel';sentinel.write_bytes(b'preserve\n')
        file=parent/'existing-file';file.write_bytes(b'preserve file\n')
        alias=parent/'release-alias';alias.symlink_to(ROOT,target_is_directory=True)
        dangling=parent/'dangling';dangling.symlink_to(parent/'not-created')
        cases=[
          ('replay-in-release','verify_release.py',['--replay','--workdir',str(ROOT)],'Replay directory must be external',None),
          ('replay-in-evidence','verify_release.py',['--replay','--workdir',str(ROOT/'evidence')],'Replay directory must be external',None),
          ('receipt-in-release','verify_release.py',['--replay','--receipt-dir',str(ROOT/'new-receipts')],'Receipt directory must be external',None),
          ('receipt-symlink-alias','verify_release.py',['--replay','--receipt-dir',str(alias/'new-receipts')],'Receipt directory must be external',None),
          ('receipt-existing-directory','verify_release.py',['--replay','--receipt-dir',str(existing)],'Receipt directory must be new',None),
          ('receipt-existing-file','verify_release.py',['--replay','--receipt-dir',str(file)],'Receipt directory must be new',None),
          ('receipt-dangling-symlink','verify_release.py',['--replay','--receipt-dir',str(dangling)],'Receipt directory must be new',None),
          ('receipt-missing-parent','verify_release.py',['--replay','--receipt-dir',str(parent/'missing'/'receipts')],'Receipt directory parent must already exist',None),
          ('pdf-dangling-symlink','build_pdf.py',['--output',str(dangling)],'PDF build directory must be fresh',None),
          ('pdf-in-release','build_pdf.py',['--output',str(ROOT)],'PDF build directory must be external',None),
          ('pdf-in-evidence','build_pdf.py',['--output',str(ROOT/'evidence'/'new-build')],'PDF build directory must be external',None),
          ('pdf-existing-directory','build_pdf.py',['--output',str(existing)],'PDF build directory must be fresh',None),
          ('pdf-existing-file','build_pdf.py',['--output',str(file)],'PDF build directory must be fresh',None),
          ('unsafe-temp-parent','verify_release.py',['--replay'],'Temporary parent must be outside the release',dict(os.environ,TMPDIR=str(ROOT))),
        ]
        if stage in ('final','engineering-preview'):
            cases += [
             ('archive-dangling-symlink','archive_release.py',['--allow-engineering-preview','--create',str(dangling)],'Refusing to overwrite an existing archive',None),
             ('archive-in-release','archive_release.py',['--allow-engineering-preview','--create',str(ROOT/'new.zip')],'Archive must be external',None),
             ('archive-existing-file','archive_release.py',['--allow-engineering-preview','--create',str(file)],'Refusing to overwrite an existing archive',None)]
        for optimized in (False,True):
            for label,script,args,message,env in cases:
                result=invoke(script,args,optimized,env)
                need(result.returncode!=0 and message in result.stderr,'Wrong rejection: '+label+': '+result.stderr[-1500:])
                need(snapshot()==before,'Source changed on output-guard test: '+label)
                need(sentinel.read_bytes()==b'preserve\n' and file.read_bytes()==b'preserve file\n','Existing output changed')
                need(not (parent/'missing').exists(),'Missing output parent was created')
                rows.append({'case':label,'optimized':optimized,'rejected_without_source_or_existing_output_mutation':True})
    with tempfile.TemporaryDirectory(prefix='report41-checker-guards-',dir=external_temp_parent()) as tmp:
        parent=Path(tmp); work=parent/'copied-release'
        shutil.copytree(ROOT,work,copy_function=shutil.copy2)
        check=subprocess.run([sys.executable,'-I','-B',str(work/'verify_release.py'),'--verify-only'],capture_output=True,text=True,timeout=120)
        need(check.returncode==0,'Copied identity failed before checker guard executions: '+check.stderr)
        plan=json.loads((work/'verification/replay-plan.json').read_bytes())
        for optimized in (False,True):
            for spec in plan['checks']:
                base=[sys.executable,'-I','-B']+(['-O'] if optimized else [])+[str(work/spec['script'])]
                saved=work/spec['receipt']
                existing=parent/'existing-receipt';existing.write_bytes(b'preserve receipt\n')
                packet_message='Packet output forbidden' if spec['script'].startswith('smooth/') else 'Refusing output inside frozen packet'
                existing_message='Fresh output required' if spec['script'].startswith('smooth/') else 'Output must be a fresh external path'
                for label,target,message in [('packet',saved,packet_message),('existing',existing,existing_message)]:
                    done=subprocess.run(base+['--output',str(target)],capture_output=True,text=True,timeout=1800)
                    need(done.returncode!=0 and message in done.stderr,'Frozen guard failure: '+spec['label']+' '+label)
                    need(existing.read_bytes()==b'preserve receipt\n','Existing receipt overwritten')
                    rows.append({'case':spec['label']+'-'+label,'optimized':optimized,'rejected_without_source_or_existing_output_mutation':True})
                out=parent/(spec['label']+('-O' if optimized else '')+'.json')
                done=subprocess.run(base+['--expect',str(saved),'--output',str(out)],capture_output=True,timeout=1800)
                need(done.returncode==0 and done.stdout==saved.read_bytes()==out.read_bytes() and not done.stderr,'Fresh external checker output failure')
                rows.append({'case':spec['label']+'-fresh-external','optimized':optimized,'exact_receipt_bytes':True})
        check=subprocess.run([sys.executable,'-I','-B',str(work/'verify_release.py'),'--verify-only'],capture_output=True,text=True,timeout=120)
        need(check.returncode==0,'Copied identity changed during checker guard tests')
    need(snapshot()==before,'Original release changed during checker guard tests')
    print(json.dumps({'schema':'report41-output-guard-regression-v1','status':'PASS','release_stage':stage,'cases':rows,'source_bytes_modes_mtimes_preserved':True,'direct_checker_output_scope':'scientific packet only; unsupported for enclosing release writes','supported_replay_output':'captured stdout; optional external new receipt directory only'},indent=2,sort_keys=True))


if __name__=='__main__':main()
