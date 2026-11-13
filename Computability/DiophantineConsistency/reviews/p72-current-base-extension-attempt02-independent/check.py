#!/usr/bin/env python3
"""Read-only post-run audit of retained per-stage evidence; no Lean invocation."""
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];root=D.parents[1]
out=Path('/tmp/p72-current-base-extension-attempt02-20261105')
survey=D/'research/p72-current-base-source-survey/result.json'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(survey)=='29cb091647eb0800936795ac0494e5cedcbe8d770c076814e8d52f9c7a738954'
s=json.loads(survey.read_text());order=s['extension_order'];sources=s['project_sources'];snap=json.loads((out/'source-snapshot.json').read_text());state=json.loads((out/'progress.json').read_text())
assert state['status']=='PASS' and state['phase']=='complete' and state['total']==state['completed']==state['source_snapshot_count']==len(order)==len(set(order))==681
assert state['driver_sha256']=='04361b39845447f6f2a45f8997a26b6c58e7e695f1bae5dc0008f617f2972322'
assert sha(out/'source-snapshot.json')==state['source_snapshot_sha256']=='4536c44c399dc42037b692a39a36cc74c807693e1e5a76e2f5db299691fff7d8'
assert state['base_checks_before']==state['base_checks_after']=={'direct_edges':2647,'distinct_direct_paths':971,'output_slots':9180,'shared_modules':918}
assert set(snap)==set(order) and sha(out/'base-links.json')==state['base_links_sha256'] and sha(out/'external-guard-before.json')==state['external_guard_before_sha256']
links=json.loads((out/'base-links.json').read_text());assert len(links)==1000
for p,v in links.items():assert Path(p).is_symlink() and str(Path(p).resolve())==v
cache={}
def checkfile(p,h,real=None):
 p=Path(p);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 key=str(p.resolve())
 if key not in cache:cache[key]=sha(p)
 assert cache[key]==h
def checkguard(guard):
 for p,v in guard.items():
  if v is None:assert not os.path.lexists(p),p
  else:checkfile(p,v['sha256'],v['realpath'])
checkguard(json.loads((out/'external-guard-before.json').read_text()))
produced={};row_hashes={};peak=0;low=None;edges=0;guard_slots=0;endpoint_reports={}
for i,n in enumerate(order):
 row=out/'rows'/f'{i:04d}.json';rec=json.loads(row.read_text());row_hashes[n]=sha(row)
 assert rec['status']=='PASS' and rec['index']==i and rec['module']==n and rec['source_sha256']==snap[n]==sources[n]['source_sha256']
 checkfile(out/'src'/(n.replace('.','/')+'.lean'),snap[n]);checkfile(root/sources[n]['source'],snap[n])
 assert len(rec['runs'])==2
 for typ,run in zip(('deps','compile'),rec['runs']):
  assert run['exit']==0 and run['stop_reason'] is None and not run['monitor_errors'] and not run['observed_descendant_pids']
  assert run['rss_limit_bytes']==5*1024**3 and run['host_floor_bytes']==10*1024**3 and run['timeout_seconds']==180
  checkfile(run['log'],run['log_sha256']);assert Path(run['log'])==out/'logs'/f'{i:04d}-{typ}.txt'
  peak=max(peak,run['peak_session_rss_bytes']);v=run['min_host_available_bytes'];low=v if low is None else min(low,v)
 deps=rec['dependencies'];assert set(deps)-{'Init'}==set(sources[n]['imports'])-{'Init'}
 for dep,v in deps.items():
  checkfile(v['path'],v['sha256'],v['realpath']);edges+=1
  if dep in set(order):assert dep in produced and produced[dep]==v['sha256'] and not Path(v['path']).is_symlink()
 guard_slots+=len(rec['direct_guard']);checkguard(rec['direct_guard'])
 text=(out/'logs'/f'{i:04d}-compile.txt').read_text()
 assert not re.search(r"(?im)^.*(?:error:|error\([^)]*\):|\bsorryAx\b|declaration uses .sorry.).*$",text)
 obj=out/'lib'/(n.replace('.','/')+'.olean');checkfile(obj,rec['object_sha256']);produced[n]=rec['object_sha256']
 if 'axiom_reports' in rec:
  reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)
  assert [list(x) for x in reports]==rec['axiom_reports']
  assert all(set(x.strip() for x in values.split(',') if x.strip())=={'propext','Classical.choice','Quot.sound'} for _,values in reports)
  endpoint_reports[n]=[name for name,_ in reports]
assert sha(out/'rows/0680.json')==state['last_row_sha256']
assert set(endpoint_reports)=={'DiophantineConsistency.Compact44.IPRAOrdinary72','DiophantineConsistency.Compact44.IPRAOrdinary72P14'}
assert len(endpoint_reports['DiophantineConsistency.Compact44.IPRAOrdinary72'])==4 and len(endpoint_reports['DiophantineConsistency.Compact44.IPRAOrdinary72P14'])==5
print(json.dumps({'status':'PASS_RETAINED_STAGE_AUDIT','progress_sha256':sha(out/'progress.json'),'source_modules':len(order),'successful_runs':2*len(order),'direct_edges':edges,'direct_guard_slots':guard_slots,'unique_file_hashes':len(cache),'endpoint_reports':endpoint_reports,'endpoint_object_sha256':{n:produced[n] for n in endpoint_reports},'endpoint_row_sha256':{n:row_hashes[n] for n in endpoint_reports},'max_sampled_session_rss':peak,'min_sampled_host_available':low,'scope':'Point-in-time retained stage/provider/guard audit; does not independently observe outer session exit, reconstruct full transitive or dynamic dependencies, or re-run Lean.'},indent=2,sort_keys=True))
