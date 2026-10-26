#!/usr/bin/env python3
"""Reused/adapted offline support. Hash and patch checks are NOT Lean checking.
Never executes Lean, Lake, repository generators, network or installs.
All patch application happens in a disposable copy, never sources/.
"""
import argparse, hashlib, json, re, shutil, subprocess, tempfile
from pathlib import Path
from plan_tools import inspect_plan, PIN
MATHLIB_PIN='81a5d257c8e410db227a6665ed08f64fea08e997'
GROUPS=['machine','encoding','rows']

def sha256(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def blob_sha(data): return hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
def verify_manifest(bundle,name):
    m=json.loads((bundle/'provenance'/name).read_text());errors=[];root=(bundle/('dependencies' if name=='dependency_manifest.json' else 'sources')).resolve()
    if m.get('commit')!=PIN:errors.append(name+': wrong pin')
    if not m.get('sources'):errors.append(name+': empty manifest')
    seen=set()
    for item in m.get('sources',[]):
        path=item['path'];p=(root/path).resolve()
        if path in seen:errors.append(path+': duplicate manifest entry')
        seen.add(path)
        if not p.is_relative_to(root) or not p.is_file():errors.append(path+': missing or escaping source');continue
        data=p.read_bytes()
        if blob_sha(data)!=item['sha'] or hashlib.sha256(data).hexdigest()!=item['sha256']:errors.append(path+': hash mismatch')
    return {'manifest':name,'checked':len(m.get('sources',[])),'errors':errors}

def verify_evidence(bundle):
    entries=[];errors=[]
    root=bundle/'encoding/evidence'
    for x in json.loads((root/'manifest.json').read_text()):
        p=root/x['local'];raw=p.read_bytes();ok=x['commit']==MATHLIB_PIN and blob_sha(raw)==x['git_blob'] and sha256(p)==x['sha256']
        entries.append(dict(path=str(p.relative_to(bundle)),git_blob_sha1=blob_sha(raw),sha256=sha256(p),status='PASS' if ok else 'FAIL'))
        if not ok:errors.append(str(p)+': evidence hash or pin mismatch')
    root=bundle/'machine/evidence';x=json.loads((root/'MathlibAbs-source.json').read_text());p=root/'MathlibAbs.lean';raw=p.read_bytes()
    ok=x['ref']==MATHLIB_PIN and blob_sha(raw)==x['sha'] and sha256(p)==x['local_sha256']
    entries.append(dict(path=str(p.relative_to(bundle)),git_blob_sha1=blob_sha(raw),sha256=sha256(p),status='PASS' if ok else 'FAIL'))
    if not ok:errors.append(str(p)+': evidence hash or pin mismatch')
    lock=json.loads((bundle/'sources/lake-manifest.json').read_text())
    if not any(p.get('name')=='mathlib' and p.get('rev')==MATHLIB_PIN for p in lock['packages']):errors.append('Mathlib evidence pin does not match repository lock')
    return dict(entries=entries,errors=errors)

def validate(bundle):
    before=[verify_manifest(bundle,n) for n in ['source_manifest.json','dependency_manifest.json']];errors=[e for r in before for e in r['errors']]
    plan=inspect_plan(json.loads((bundle/'validation/replay_plan.json').read_text()),bundle);errors+=plan['errors']
    evidence=verify_evidence(bundle);errors+=evidence['errors']
    candidates=[dict(source=p['source'],sha256=sha256(bundle/p['source']),expected_endpoints=len(p['expected'])) for p in plan['probes']]
    patches=sorted(p for g in GROUPS for p in (bundle/g).glob('*.patch'));results=[]
    if len(patches)!=6:errors.append('Expected exactly six proposed patches, found '+str(len(patches)))
    if not shutil.which('git'):errors.append('git unavailable for disposable patch checks')
    else:
      with tempfile.TemporaryDirectory(prefix='proveit-round3-source-check-') as td:
        copy=Path(td)/'source-copy';shutil.copytree(bundle/'sources',copy)
        for patch in patches:
          result=dict(path=str(patch.relative_to(bundle)),sha256=sha256(patch),git_apply_check_passed=False,applied_in_disposable_copy=False)
          body=patch.read_text();headers=re.findall(r'^\+\+\+ b/(.*)$',body,re.M)
          if not headers or any(Path(n).is_absolute() or '..' in Path(n).parts for n in headers):
            errors.append(result['path']+': no safe target paths');results.append(result);continue
          check=subprocess.run(['git','apply','--check','--',str(patch.resolve())],cwd=copy,capture_output=True,text=True)
          result.update(check_exit=check.returncode,check_stderr=check.stderr)
          if check.returncode:errors.append(result['path']+': git apply --check failed')
          else:
            result['git_apply_check_passed']=True
            applied=subprocess.run(['git','apply','--',str(patch.resolve())],cwd=copy,capture_output=True,text=True)
            result.update(apply_exit=applied.returncode,apply_stderr=applied.stderr,applied_in_disposable_copy=not applied.returncode)
            if applied.returncode:errors.append(result['path']+': disposable application failed')
            else:
              result['resulting_target_sha256']={n:sha256(copy/n) for n in headers}
              result['matches_complete_proposed_modules']={}
              for n in headers:
                if patch.parent.name=='machine':proposed=bundle/'machine/patched'/n
                elif patch.parent.name=='encoding':proposed=bundle/'encoding/WangMachineEncodingCandidate.lean'
                else:proposed=bundle/'rows/proposed'/Path(n).name
                ok=proposed.is_file() and sha256(copy/n)==sha256(proposed)
                result['matches_complete_proposed_modules'][str(proposed.relative_to(bundle))]=ok
                if not ok:errors.append(result['path']+': patched bytes differ from complete proposed module')
          result['added_physical_lines']=sum(l.startswith('+') and not l.startswith('+++') for l in body.splitlines())
          result['removed_physical_lines']=sum(l.startswith('-') and not l.startswith('---') for l in body.splitlines())
          results.append(result)
    after=[verify_manifest(bundle,n) for n in ['source_manifest.json','dependency_manifest.json']];errors += [e for r in after for e in r['errors']]
    active=bundle/'sources/Computability/DiophantineConsistency/Lean'
    source_counts={'selected':before[0]['checked'],'separate_BusyBeaver_dependencies':before[1]['checked'],'active_DiophantineConsistency_Lean_files':len(list(active.rglob('*.lean')))}
    if source_counts!={'selected':860,'separate_BusyBeaver_dependencies':5,'active_DiophantineConsistency_Lean_files':608}:errors.append('Unexpected source counts: '+repr(source_counts))
    return dict(status='PASS_SOURCE_ONLY_UNCOMPILED' if not errors else 'FAIL',pin=PIN,source_counts=source_counts,source_hashes_before=before,source_hashes_after=after,library_evidence=evidence,plan=plan,candidates=candidates,patches=results,errors=errors,not_established=['Lean elaboration','kernel checking','transitive axiom results','composite assumed-adopted baseline build','integration correctness','performance improvement'])

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--bundle',type=Path,default=Path(__file__).resolve().parents[1]);ap.add_argument('--json',type=Path);a=ap.parse_args()
    r=validate(a.bundle.resolve());text=json.dumps(r,indent=2)+'\n'
    if a.json:a.json.write_text(text)
    print(text);raise SystemExit(bool(r['errors']))
if __name__=='__main__':main()
