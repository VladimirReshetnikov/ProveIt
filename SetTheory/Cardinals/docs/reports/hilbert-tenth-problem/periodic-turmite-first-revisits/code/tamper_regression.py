#!/usr/bin/env python3
"""Reject Report38 tampering at the identity gate before scientific execution."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
SOURCE = 'evidence/source-packet/'


def need(ok,message):
    if ok is not True:raise RuntimeError(message)


def invoke(root,mode,optimized=False,extra=(),env=None):
    return subprocess.run([sys.executable,'-I','-B']+(['-O'] if optimized else [])+[str(root/'verify_release.py'),mode]+list(extra),capture_output=True,text=True,timeout=120,env=env)


def snapshot(root=ROOT):
    result = {}
    for p in [root]+sorted(root.rglob('*')):
        s = p.lstat()
        need(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode), 'Unsafe source path')
        result[p.relative_to(root).as_posix()] = (hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None,stat.S_IMODE(s.st_mode),s.st_mtime_ns)
    return result


def external_temp_parent():
    candidates = [os.environ[k] for k in ('TMPDIR','TEMP','TMP') if os.environ.get(k)]+['/tmp','/var/tmp']
    for value in candidates:
        candidate = Path(value).resolve()
        need(candidate != ROOT and ROOT not in candidate.parents, 'Temporary parent must be outside the release')
        if candidate.is_dir() and os.access(candidate,os.W_OK|os.X_OK):return candidate
    raise RuntimeError('No writable external temporary parent is available')


def main():
    before = snapshot()
    baseline = invoke(ROOT,'--verify-only')
    need(baseline.returncode == 0, 'Baseline identity failed: '+baseline.stderr)
    changed = {name:name for name in ('verify_release.py','seal_release.py','build_pdf.py','archive_release.py','archive_regression.py','tamper_regression.py')}
    for name in ('one_visit.py','observations.py','test_boundary_regression.py','test_observations.py','independent_checks.py','example.py','verify_release.py','boundary-context/one_visit.py','boundary-context/test_one_visit.py','boundary-context/review_checks.py','boundary-context/examples.json','PROOF.md','manifest-sha256.json','author-normal.log','independent-normal.log','release-receipt.json'):
        changed['source-'+name] = SOURCE+name
    for name in ('source-lineage.json','replay-plan.json','expected-receipts.json'):
        changed[name] = 'verification/'+name
    cases = list(changed)+['manifest','manifest-and-checksums','receipt','bool-for-int','float-for-int','extra-receipt-key','malformed-json','duplicate-json-key','extra-file','extra-directory','symlink','missing-file','file-mode','directory-mode','checksums']
    rows = []
    for optimized in (False,True):
        for case in cases:
            with tempfile.TemporaryDirectory(prefix='report38-tamper-',dir=external_temp_parent()) as tmp:
                work = Path(tmp)/'relocated-release'
                shutil.copytree(ROOT,work,copy_function=shutil.copy2)
                if case in changed:
                    p = work/changed[case];p.write_bytes(p.read_bytes()+b'\n# tamper probe\n')
                elif case in ('manifest','manifest-and-checksums'):
                    p=work/'MANIFEST.json';v=json.loads(p.read_bytes());v['file_count']+=1;p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
                    if case=='manifest-and-checksums':
                        (work/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(work).as_posix()+'\n' for p in sorted(work.rglob('*')) if p.is_file() and p.name!='SHA256SUMS'))
                elif case in ('receipt','bool-for-int','float-for-int','extra-receipt-key','malformed-json','duplicate-json-key'):
                    p=work/SOURCE/'example-result.json';v=json.loads(p.read_bytes())
                    if case=='receipt':v['compressed_lanes']+=1
                    elif case=='bool-for-int':v['compressed_lanes']=True
                    elif case=='float-for-int':v['compressed_lanes']=float(v['compressed_lanes'])
                    elif case=='extra-receipt-key':v['extra']=0
                    if case=='malformed-json':p.write_text('{')
                    elif case=='duplicate-json-key':p.write_text('{"x":1,"x":1}')
                    else:p.write_text(json.dumps(v,indent=2)+'\n')
                elif case=='extra-file':(work/'unexpected.py').write_text('raise RuntimeError("must not execute")\n')
                elif case=='extra-directory':(work/'unexpected-directory').mkdir()
                elif case=='symlink':(work/'unexpected-link').symlink_to(SOURCE+'README.md')
                elif case=='missing-file':(work/SOURCE/'boundary-context/one_visit.py').unlink()
                elif case=='file-mode':(work/SOURCE/'README.md').chmod(0o600)
                elif case=='directory-mode':(work/'evidence').chmod(0o700)
                else:
                    p=work/'SHA256SUMS';p.write_bytes(p.read_bytes()+b'\n')
                done=invoke(work,'--replay',optimized)
                need(done.returncode!=0,'Tampered package accepted: '+case)
                need('Identity gate:' in done.stderr,'Wrong rejection stage: '+case+': '+done.stderr)
                rows.append({'case':case,'optimized':optimized,'identity_gate_rejected_before_payload_execution':True})
    boundaries=[]
    for optimized in (False,True):
        for case in ('root-output','nested-output','tmpdir-root','tmpdir-nested','symlink-output'):
            with tempfile.TemporaryDirectory(prefix='report38-path-',dir=external_temp_parent()) as tmp:
                work=Path(tmp)/'release';shutil.copytree(ROOT,work,copy_function=shutil.copy2)
                initial=snapshot(work);env=dict(os.environ);extra=()
                if case=='root-output':extra=('--workdir',str(work))
                elif case=='nested-output':extra=('--workdir',str(work/'must-not-exist'))
                elif case=='symlink-output':
                    link=Path(tmp)/'external-looking-link';link.symlink_to(work,target_is_directory=True);extra=('--workdir',str(link/'must-not-exist'))
                else:env['TMPDIR']=str(work if case=='tmpdir-root' else work/'must-not-exist')
                done=invoke(work,'--replay',optimized,extra,env)
                need(done.returncode!=0 and 'outside the release' in done.stderr,'Unsafe replay output path not rejected: '+case)
                need(snapshot(work)==initial,'Unsafe output rejection changed the release: '+case)
                boundaries.append({'case':case,'optimized':optimized,'rejected_without_release_mutation':True})
    types={}
    for mode,optimized in [('normal',False),('optimized',True)]:
        result=invoke(ROOT,'--self-test-types',optimized)
        need(result.returncode==0,'Strict JSON self-test failed');types[mode]=json.loads(result.stdout)
    need(types['normal']==types['optimized'],'Strict type results differ')
    need(snapshot()==before,'Original release bytes/modes/mtimes changed')
    print(json.dumps({'schema':'report38-tamper-regression-v1','status':'PASS','cases':rows,'output_boundaries':boundaries,'strict_json':types,'original_bytes_modes_mtimes_preserved':True},indent=2,sort_keys=True))


if __name__=='__main__':main()
