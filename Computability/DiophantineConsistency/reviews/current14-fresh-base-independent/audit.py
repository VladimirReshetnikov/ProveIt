#!/usr/bin/env python3
"""Read-only terminal audit of the single current14 fresh-project build."""
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
TASK=ROOT/'Computability/DiophantineConsistency'
WATCHDOG=TASK/'research/current14-standard-fresh-rebuild-preflight/run-observation.json'
RUNNER=TASK/'research/current14-standard-fresh-rebuild-preflight/run.py'
BASE=Path('/tmp/current14-standard-fresh-build-20261104')
SNAP=Path('/tmp/current14-standard-fresh-source-20261104')
PROVIDER=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json')
RESULT=HERE/'receipt.json'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash',
          '.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
EXPECTED={'snapshot':'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',
          'provider':'7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6',
          'runner':'790a4b13f96f5cd544981aab6bdc7ae9e573a32f14195505551e191f0ee0a212',
          'driver':'8170bd401b1821666fffc2a55f8dd908e473d32c71797661a5acd85a32d0dc56'}
def need(ok,why):
    if not ok:raise ValueError(why)
def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for buf in iter(lambda:f.read(1048576),b''):h.update(buf)
    return h.hexdigest()
def guard(g):
    for name,entry in g.items():
        p=Path(name)
        if entry is None:need(not os.path.lexists(p),('unexpected path',name))
        else:need(p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256'],('guard drift',name))
need(not RESULT.exists(),'refusing existing receipt')
wd=json.loads(WATCHDOG.read_text())
need(wd.get('status')=='PASS' and wd.get('exit')==0 and wd.get('build_status')=='PASS',('build not terminal PASS',wd.get('status'),wd.get('exit')))
need(wd.get('build_source_status')=='CURRENT_AT_FINAL_CHECK' and wd.get('build_source_drift')==[], 'build was not source-current')
wdhash=sha(WATCHDOG);statepath=BASE/'state.json';need(sha(statepath)==wd['build_state_sha256'],'watchdog/base state mismatch')
state=json.loads(statepath.read_text());manifestpath=SNAP/'manifest.json'
need(sha(manifestpath)==EXPECTED['snapshot'] and sha(PROVIDER)==EXPECTED['provider'] and sha(RUNNER)==EXPECTED['runner'],'snapshot/provider/runner mismatch')
need(wd['driver_sha256']==EXPECTED['driver'] and state['driver_sha256']==EXPECTED['driver'], 'driver hash mismatch')
need(state['status']=='PASS' and state['source_status']=='CURRENT_AT_FINAL_CHECK' and state['workspace_source_drift']==[], 'base is not current PASS')
need(state['manifest_sha256']==EXPECTED['snapshot'] and state['provider_receipt_sha256']==EXPECTED['provider'],'state pin mismatch')
m=json.loads(manifestpath.read_text());names=m['order'];rows=m['sources'];records=state['records'];outputs=state['outputs']
target='DiophantineConsistency.IPRAStandardCurrentEndpointChecks'
need(len(names)==len(set(names))==len(records)==len(outputs)==1000 and m['target']==names[-1]==target, 'wrong module inventory')
need([r['module'] for r in records]==names and all(r['exit']==0 for r in records),'row order or exit mismatch')
need(sha(ROOT/'lakefile.toml')==m['lakefile_sha256'] and sha(ROOT/'lean-toolchain')==m['lean_toolchain_sha256'],'configuration drift')
lib=BASE/'lib';pkg=Path(state['package_overlay']);lean=Path(state['lean_path']);tool=lean.resolve().parent.parent/'lib/lean'
need(sha(lean)==state['lean_sha256'],'Lean executable mismatch')
target_names=['DiophantineConsistency.IPRAStandardTheory.leibniz',
              'DiophantineConsistency.IPRAStandardTheory.provable_iff',
              'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_consistency',
              'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_translated_consistency']
paths=[];direct_edges=0
for rec in records:
    name=rec['module'];row=rows[name];src=SNAP/row['snapshot_path'];work=ROOT/row['workspace_path'];paths.append(row['workspace_path'])
    need(src==SNAP/'src'/(name.replace('.','/')+'.lean') and src.is_file() and not src.is_symlink() and
         all(not (SNAP/'src'/p).is_symlink() for p in src.relative_to(SNAP/'src').parents),('snapshot path issue',name))
    need(work.is_file() and sha(work)==sha(src)==row['sha256']==rec['source_sha256'],('source drift',name))
    stem=lib/name.replace('.','/');obj=Path(str(stem)+'.olean');g=outputs[name]
    need(set(g)=={str(stem)+s for s in SUFFIXES},('incomplete output guard',name))
    need(obj.is_file() and not obj.is_symlink() and sha(obj)==rec['object_sha256'] and
         isinstance(g[str(obj)],dict) and g[str(obj)]['sha256']==rec['object_sha256'],('output mismatch',name))
    guard(g)
    log=Path(rec['log']);need(log.is_file() and sha(log)==rec['log_sha256'],('log mismatch',name));text=log.read_text()
    need(not re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b',text),('error or sorry in log',name))
    if name==target:
        reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
        need([n for n,_ in reports]==target_names and [a for _,a in reports]==rec['axiom_reports'], 'target axiom report mismatch')
        need(all(not ({x.strip() for x in a.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}) for _,a in reports), 'unexpected target axiom')
    direct=rec['direct_inputs'];declared=set(row['imports']);actual=set(direct)
    need(declared<=actual and not actual-declared-{'Init'},('declared/direct mismatch',name))
    for module,entry in direct.items():
        direct_edges+=1;path=Path(entry['path']);expected_root=lib if module in rows else {'package':pkg,'toolchain':tool}.get(entry['kind'])
        need(expected_root is not None and path==expected_root/(module.replace('.','/')+'.olean'),('direct root mismatch',name,module))
        need(entry['kind']==('project' if module in rows else entry['kind']),('wrong project kind',name,module))
        guarded=state['guarded_companions'].get(str(path))
        need(isinstance(guarded,dict) and guarded['sha256']==entry['sha256'],('direct guard mismatch',name,module))
guard(state['guarded_companions'])
pr=json.loads(PROVIDER.read_text());need(pr['status']=='BUILT' and pr['exit_code']==0,'Foundation provider not built')
foundation=Path(pr['root'])/'.lake/build/lib/lean/Foundation'
need((pkg/'Foundation').resolve(strict=True)==foundation.resolve(strict=True),'Foundation root mismatch')
guard(pr['declared_external_guard'])
for rel,h in pr['foundation_artifacts'].items():
    p=foundation/rel;need(p.is_file() and not p.is_symlink() and sha(p)==h,('Foundation artifact mismatch',rel))
actual={str(p.relative_to(foundation)) for p in foundation.rglob('*') if p.is_file() or p.is_symlink()}
need(actual==set(pr['foundation_artifacts']),'Foundation inventory mismatch')
def gitset(*args):return {p.decode() for p in subprocess.check_output(['git',*args,'--',*paths],cwd=ROOT).split(b'\0') if p}
need(gitset('ls-files','-z')==set(paths),'snapshot sources no longer all tracked')
need(not gitset('diff','--name-only','-z','HEAD'),'workspace source differs from HEAD')
for rec in records:
    name=rec['module'];row=rows[name]
    need(sha(ROOT/row['workspace_path'])==row['sha256'] and sha(SNAP/row['snapshot_path'])==row['sha256'],('final source drift',name))
    need(sha(rec['log'])==rec['log_sha256'],('final log drift',name))
    guard(outputs[name])
guard(state['guarded_companions']);guard(pr['declared_external_guard'])
for rel,h in pr['foundation_artifacts'].items():
    p=foundation/rel;need(p.is_file() and not p.is_symlink() and sha(p)==h,('final Foundation drift',rel))
need({str(p.relative_to(foundation)) for p in foundation.rglob('*') if p.is_file() or p.is_symlink()}==actual,
     'Foundation inventory changed during audit')
need(not gitset('diff','--name-only','-z','HEAD'),'workspace source differs from final HEAD')
need(sha(manifestpath)==EXPECTED['snapshot'] and sha(PROVIDER)==EXPECTED['provider'] and sha(RUNNER)==EXPECTED['runner'],
     'snapshot, provider or runner changed during audit')
need(sha(statepath)==wd['build_state_sha256'] and sha(WATCHDOG)==wdhash,'terminal evidence changed during audit')
receipt={'status':'PASS_SINGLE_SOURCE_CURRENT_ARTIFACT_AUDIT','watchdog_sha256':wdhash,
         'base_state_sha256':wd['build_state_sha256'],'snapshot_sha256':EXPECTED['snapshot'],
         'provider_sha256':EXPECTED['provider'],'source_count':len(names),'direct_edges':direct_edges,
         'guarded_companions':len(state['guarded_companions']),'foundation_artifacts':len(actual),
         'target_axioms':reports,'current_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
         'audit_sha256':sha(__file__),
         'scope':'One source-current project build, artifact and recorded direct-import checks. No second Lean replay; package-transitive, dynamic and transient-mutation ancestry inherited.'}
with RESULT.open('x') as f:json.dump(receipt,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(receipt,sort_keys=True))
