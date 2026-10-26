#!/usr/bin/env python3
"""Offline source/hash checks and git-apply checks IN A DISPOSABLE COPY ONLY.
No Lean/Lake execution, source snapshot mutation, network or dependency install.
"""
import argparse, hashlib, json, re, shutil, subprocess, tempfile
from pathlib import Path
from plan_tools import inspect_plan, PIN

def sha256(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def verify_sources(bundle):
    m=json.loads((bundle/'provenance/source_manifest.json').read_text()); errors=[]
    if m.get('commit')!=PIN: errors.append('Manifest pin mismatch')
    if not m.get('sources'):errors.append('Empty source manifest')
    for item in m.get('sources',[]):
        p=(bundle/'sources'/item['path']).resolve()
        if not p.is_relative_to((bundle/'sources').resolve()) or not p.is_file(): errors.append(item['path']+': missing or escaping source');continue
        data=p.read_bytes(); blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if blob!=item['sha'] or hashlib.sha256(data).hexdigest()!=item['sha256']: errors.append(item['path']+': hash mismatch')
    return {'checked':len(m.get('sources',[])),'errors':errors}

def validate(bundle):
    before=verify_sources(bundle); errors=list(before['errors'])
    plan=inspect_plan(json.loads((bundle/'validation/replay_plan.json').read_text()),bundle); errors+=plan['errors']
    evidence=bundle/'supplemental/evidence/MRDPCore.lean'
    em=json.loads((bundle/'supplemental/evidence/MRDPCore_manifest.json').read_text())
    raw=evidence.read_bytes(); blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    evidence_ok=em.get('commit')==PIN and blob==em['sha'] and sha256(evidence)==em['sha256']
    if not evidence_ok: errors.append('Supplemental MRDPCore pinned byte verification failed')
    supplemental_source={'path':str(evidence.relative_to(bundle)),'git_blob_sha1':blob,'sha256':sha256(evidence),'status':'PASS' if evidence_ok else 'FAIL'}
    candidates=[dict(source=p['source'],sha256=sha256(bundle/p['source']),expected_endpoints=len(p['expected'])) for p in plan['probes']]
    patches=sorted(p for group in ['annotated','current','wang','supplemental'] for p in (bundle/group).glob('*.patch'))
    patch_results=[]
    if not patches: errors.append('No proposed patches; refusing vacuous patch-application claim')
    if not shutil.which('git'): errors.append('git unavailable for disposable-copy patch checks')
    else:
        with tempfile.TemporaryDirectory(prefix='proveit-round2-source-check-') as td:
            copy=Path(td)/'source-copy';shutil.copytree(bundle/'sources',copy)
            for patch in patches:
                result={'path':str(patch.relative_to(bundle)),'sha256':sha256(patch),'git_apply_check_passed':False,'applied_in_disposable_copy':False}
                body=patch.read_text(); headers=re.findall(r'^\+\+\+ b/(.*)$',body,re.M)
                if not headers or any(Path(n).is_absolute() or '..' in Path(n).parts for n in headers):
                    result['error']='No safe target paths';errors.append(result['path']+': invalid patch');patch_results.append(result);continue
                check=subprocess.run(['git','apply','--check','--',str(patch.resolve())],cwd=copy,capture_output=True,text=True)
                result['check_exit']=check.returncode; result['check_stderr']=check.stderr
                if check.returncode: errors.append(result['path']+': git apply --check failed')
                else:
                    result['git_apply_check_passed']=True
                    applied=subprocess.run(['git','apply','--',str(patch.resolve())],cwd=copy,capture_output=True,text=True)
                    result['apply_exit']=applied.returncode;result['apply_stderr']=applied.stderr
                    result['applied_in_disposable_copy']=not applied.returncode
                    if applied.returncode:errors.append(result['path']+': disposable application failed')
                    else: result['resulting_target_sha256']={n:sha256(copy/n) for n in headers}
                result['added_physical_lines']=sum(l.startswith('+') and not l.startswith('+++') for l in body.splitlines())
                result['removed_physical_lines']=sum(l.startswith('-') and not l.startswith('---') for l in body.splitlines())
                patch_results.append(result)
    after=verify_sources(bundle); errors+=after['errors']
    return dict(status='PASS_SOURCE_ONLY_UNCOMPILED' if not errors else 'FAIL',pin=PIN,source_hashes_before=before,source_hashes_after=after,supplemental_source=supplemental_source,plan=plan,candidates=candidates,patches=patch_results,errors=errors,not_established=['Lean elaboration','kernel checking','transitive axiom results','integration correctness','performance improvement'])

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--bundle',type=Path,default=Path(__file__).resolve().parents[1]);ap.add_argument('--json',type=Path)
    a=ap.parse_args();r=validate(a.bundle.resolve());text=json.dumps(r,indent=2)+'\n'
    if a.json:a.json.write_text(text)
    print(text);raise SystemExit(bool(r['errors']))
if __name__=='__main__':main()
