#!/usr/bin/env python3
"""Reject tampered bytes, inventories, modes and receipts before replay executes."""
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


def need(ok,message):
    if ok is not True:raise RuntimeError(message)


def invoke(root,mode,optimized=False):
    return subprocess.run([sys.executable,'-I','-B']+(['-O'] if optimized else [])+[str(root/'verify_release.py'),mode],capture_output=True,text=True,timeout=120)


def snapshot():
    result={}
    for p in [ROOT]+sorted(ROOT.rglob('*')):
        s=p.lstat()
        need(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode),'Unsafe source path')
        result[p.relative_to(ROOT).as_posix()]=(hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None,stat.S_IMODE(s.st_mode),s.st_mtime_ns)
    return result


def external_temp_parent():
    # Do not call tempfile.gettempdir(): its writable-directory probe can touch
    # the release itself when TMPDIR or the current directory is unsafe.
    candidates = [os.environ[k] for k in ('TMPDIR','TEMP','TMP') if os.environ.get(k)]
    candidates += ['/tmp','/var/tmp']
    for value in candidates:
        candidate = Path(value).resolve()
        need(candidate != ROOT and ROOT not in candidate.parents, 'Temporary parent must be outside the release')
        if candidate.is_dir() and os.access(candidate, os.W_OK | os.X_OK):
            return candidate
    raise RuntimeError('No writable external temporary parent is available')


def main():
    before=snapshot()
    baseline=invoke(ROOT,'--verify-only')
    need(baseline.returncode==0,'Baseline identity failed: '+baseline.stderr)
    changed={
        'jacobi-code':'jacobi/check_jacobi_addendum.py',
        'jacobi-proof':'jacobi/JACOBI-ADDENDUM.md',
        'jacobi-audit':'jacobi/INDEPENDENT-AUDIT.md',
        'jacobi-checksums':'jacobi/MANIFEST.sha256',
        'jacobi-lineage':'verification/jacobi-lineage.json',
        'jacobi-receipt':'jacobi/expected_jacobi_receipt.json',
        'jacobi-provenance':'jacobi/source_manifest.json',
        'author-code':'evidence/check_unwrapped_family.py',
        'independent-code':'evidence/independent/check_audit.py',
        'inert-upstream-code':'evidence/context/complete77.snapshot.py',
        'inert-upstream-data':'evidence/context/projection.snapshot.json',
        'verifier-code':'verify_release.py',
        'sealer-code':'seal_release.py',
        'builder-code':'build_pdf.py',
        'archiver-code':'archive_release.py',
        'tamper-tool-code':'tamper_regression.py',
        'archive-test-code':'archive_regression.py',
        'output-guard-code':'output_guard_regression.py',
        'proof':'evidence/ALL-BUT-MAIN-PROJECTION.md',
        'source-checksums':'evidence/MANIFEST.sha256',
        'source-lineage':'verification/source-lineage.json',
        'replay-plan':'verification/replay-plan.json',
        'source-manifest':'evidence/source_manifest.json',
    }
    cases=list(changed)+['manifest','manifest-and-checksums','receipt','bool-for-int','float-for-int','extra-receipt-key','malformed-json','duplicate-json-key','expected-receipt','extra-file','extra-directory','symlink','missing-file','file-mode','directory-mode','checksums','checksum-crlf']
    rows=[]
    for optimized in (False,True):
        for case in cases:
            with tempfile.TemporaryDirectory(prefix='report39-tamper-',dir=external_temp_parent()) as tmp:
                work=Path(tmp)/'relocated-release'
                shutil.copytree(ROOT,work,copy_function=shutil.copy2)
                if case in changed:
                    p=work/changed[case];p.write_bytes(p.read_bytes()+b'\n# tamper probe\n')
                elif case in ('manifest','manifest-and-checksums'):
                    p=work/'MANIFEST.json';v=json.loads(p.read_bytes());v['file_count']+=1;p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
                    if case=='manifest-and-checksums':
                        (work/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(work).as_posix()+'\n' for p in sorted(work.rglob('*')) if p.is_file() and p.relative_to(work).as_posix()!='SHA256SUMS'))
                elif case in ('receipt','bool-for-int','float-for-int','extra-receipt-key','malformed-json','duplicate-json-key'):
                    p=work/'evidence/expected_check_results.json';v=json.loads(p.read_bytes())
                    if case=='receipt':v['lattice_fixtures']['cases']+=1
                    elif case=='bool-for-int':v['lattice_fixtures']['cases']=True
                    elif case=='float-for-int':v['lattice_fixtures']['cases']=float(v['lattice_fixtures']['cases'])
                    elif case=='extra-receipt-key':v['unapproved_extra']=0
                    if case=='malformed-json':p.write_text('{')
                    elif case=='duplicate-json-key':p.write_text('{"x":1,"x":1}')
                    else:p.write_text(json.dumps(v,indent=2)+'\n')
                elif case=='expected-receipt':
                    p=work/'verification/expected-receipts.json';v=json.loads(p.read_bytes());v['evidence/expected_check_results.json']['lattice_fixtures']['cases']=True;p.write_text(json.dumps(v,indent=2)+'\n')
                elif case=='extra-file':(work/'unexpected.py').write_text('raise RuntimeError("must not execute")\n')
                elif case=='extra-directory':(work/'unexpected-directory').mkdir()
                elif case=='symlink':(work/'unexpected-link').symlink_to('evidence/README.md')
                elif case=='missing-file':(work/'evidence/context/complete77.snapshot.py').unlink()
                elif case=='file-mode':(work/'evidence/README.md').chmod(0o600)
                elif case=='directory-mode':(work/'evidence').chmod(0o700)
                elif case=='checksum-crlf':
                    p=work/'SHA256SUMS';p.write_bytes(p.read_bytes().replace(b'\n',b'\r\n'))
                else:
                    p=work/'SHA256SUMS';p.write_bytes(p.read_bytes()+b'\n')
                done=invoke(work,'--replay',optimized)
                need(done.returncode!=0,'Tampered package accepted: '+case)
                need('Identity gate:' in done.stderr,'Wrong rejection stage: '+case+': '+done.stderr)
                rows.append({'case':case,'optimized':optimized,'identity_gate_rejected_before_payload_execution':True})
    types={}
    for mode,optimized in [('normal',False),('optimized',True)]:
        result=invoke(ROOT,'--self-test-types',optimized)
        need(result.returncode==0,'Strict JSON self-test failed')
        types[mode]=json.loads(result.stdout)
    need(types['normal']==types['optimized'],'Strict type results differ')
    need(snapshot()==before,'Original release bytes/modes/mtimes changed')
    print(json.dumps({'schema':'report39-tamper-regression-v1','status':'PASS','cases':rows,'strict_json':types,'original_bytes_modes_mtimes_preserved':True},indent=2,sort_keys=True))


if __name__=='__main__':main()
