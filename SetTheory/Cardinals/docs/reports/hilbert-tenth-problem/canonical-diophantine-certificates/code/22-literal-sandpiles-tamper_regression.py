#!/usr/bin/env python3
"""Adversarial identity/JSON tests using disposable copies outside the release."""
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
    cmd=[sys.executable,'-I','-B']+(['-O'] if optimized else [])+[str(root/'verify_release.py'),mode]
    return subprocess.run(cmd,capture_output=True,text=True,timeout=120)


def snapshot():
    result={}
    for p in [ROOT]+sorted(ROOT.rglob('*')):
        s=p.lstat()
        result[p.relative_to(ROOT).as_posix()]=(hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None,stat.S_IMODE(s.st_mode),s.st_mtime_ns)
    return result


def main():
    before=snapshot()
    baseline=invoke(ROOT,'--verify-only')
    need(baseline.returncode==0,'Baseline identity failed: '+baseline.stderr)
    cases=['manifest','manifest-and-checksums','author-code','unused-helper-code','verifier-code','proof','receipt','bool-for-int','extra-receipt-key','malformed-json','duplicate-json-key','expected-receipt','extra-file','extra-directory','symlink','missing-file','file-mode','checksums']
    rows=[]
    for optimized in (False,True):
        for case in cases:
            with tempfile.TemporaryDirectory(prefix='report35-tamper-') as tmp:
                work=Path(tmp)/'relocated-release'
                shutil.copytree(ROOT,work,copy_function=shutil.copy2)
                if case in ('manifest','manifest-and-checksums'):
                    p=work/'MANIFEST.json';v=json.loads(p.read_bytes());v['file_count']+=1;p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
                    if case=='manifest-and-checksums':
                        (work/'SHA256SUMS').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(work).as_posix()+'\n' for p in sorted(work.rglob('*')) if p.is_file() and p.name!='SHA256SUMS'))
                elif case in ('author-code','unused-helper-code','verifier-code','proof'):
                    name={'author-code':'evidence/loader/compiler/literal_loader.py','unused-helper-code':'seal_release.py','verifier-code':'verify_release.py','proof':'evidence/loader/LOADER-PROOF.md'}[case]
                    p=work/name;p.write_bytes(p.read_bytes()+b'\n# tamper probe\n')
                elif case in ('receipt','bool-for-int','extra-receipt-key','malformed-json','duplicate-json-key'):
                    p=work/'evidence/loader/compiler/worked_example.json';v=json.loads(p.read_bytes())
                    if case=='receipt':v['seed_count']+=1
                    elif case=='bool-for-int':v['seed_count']=True
                    elif case=='extra-receipt-key':v['unapproved_extra']=0
                    if case=='malformed-json':p.write_text('{')
                    elif case=='duplicate-json-key':p.write_text('{"x":1,"x":1}')
                    else:p.write_text(json.dumps(v,indent=2)+'\n')
                elif case=='expected-receipt':
                    p=work/'verification/expected-receipts.json';v=json.loads(p.read_bytes());v['evidence/loader/compiler/worked_example.json']['seed_count']=True;p.write_text(json.dumps(v,indent=2)+'\n')
                elif case=='extra-file':(work/'unexpected.py').write_text('raise RuntimeError("must not execute")\n')
                elif case=='extra-directory':(work/'unexpected-directory').mkdir()
                elif case=='symlink':(work/'unexpected-link').symlink_to('evidence/loader/README.md')
                elif case=='missing-file':(work/'evidence/loader/data/u15_table.json').unlink()
                elif case=='file-mode':(work/'evidence/loader/README.md').chmod(0o600)
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
    print(json.dumps({'schema':'report35-tamper-regression-v1','status':'PASS','cases':rows,'strict_json':types,'original_bytes_modes_mtimes_preserved':True},indent=2,sort_keys=True))


if __name__=='__main__':main()
