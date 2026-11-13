#!/usr/bin/env python3
"""Recheck the 918 shared current14 base stages used by the P72 extension."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
P=Path(__file__).resolve().parent;D=P.parents[1];root=D.parents[1]
base=Path('/tmp/current14-standard-fresh-build-20261104')
state=base/'state.json';man=D/'research/current14-standard-fresh-rebuild-preflight/snapshot-manifest.json';survey=D/'research/p72-current-base-source-survey/result.json';watch=D/'research/current14-standard-fresh-rebuild-preflight/run-observation.json'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for p,h in [(state,'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014'),(man,'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749'),(survey,'29cb091647eb0800936795ac0494e5cedcbe8d770c076814e8d52f9c7a738954'),(watch,'5d45638261f749227f6530b55154b7d3c28197e1e04ab0eaffb10876e2fa3475')]:assert sha(p)==h
s=json.loads(state.read_text());m=json.loads(man.read_text());q=json.loads(survey.read_text());w=json.loads(watch.read_text())
assert s['status']=='PASS' and s['source_status']=='CURRENT_AT_FINAL_CHECK' and s['manifest_sha256']==sha(man)
assert w['exit']==0 and w['build_status']=='PASS' and w['build_state_sha256']==sha(state)
sources=q['project_sources'];shared=set(sources)&set(m['sources']);assert len(shared)==918
records={r['module']:r for r in s['records']};cache={};edges=slots=0;paths=set()
def check(p,h,real=None):
 p=Path(p);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 key=str(p.resolve())
 if key not in cache:cache[key]=sha(p)
 assert cache[key]==h
suffixes=['.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash']
for n in shared:
 r=records[n];assert r['exit']==0 and r['source_sha256']==sources[n]['source_sha256']
 check(root/sources[n]['source'],r['source_sha256']);check(r['log'],r['log_sha256'])
 stem=base/'lib'/n.replace('.','/');expected=s['outputs'][n];assert set(expected)=={str(stem)+x for x in suffixes}
 assert expected[str(stem)+'.olean']['sha256']==r['object_sha256']
 for path,v in expected.items():
  slots+=1
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 assert set(r['direct_inputs'])-{'Init'}==set(sources[n]['imports'])-{'Init'}
 for dep in r['direct_inputs'].values():edges+=1;paths.add(dep['path']);check(dep['path'],dep['sha256'])
assert (edges,slots,len(paths))==(2647,9180,971)
print(json.dumps({'status':'PASS_SHARED_BASE_RECHECK','base_state_sha256':sha(state),'shared_modules':len(shared),'direct_edges':edges,'distinct_direct_paths':len(paths),'output_slots':slots,'unique_hashed_paths':len(cache),'scope':'Retained logs, outputs and recorded direct inputs only; full transitive/package and dynamic dependencies are not reconstructed.'},indent=2,sort_keys=True))
