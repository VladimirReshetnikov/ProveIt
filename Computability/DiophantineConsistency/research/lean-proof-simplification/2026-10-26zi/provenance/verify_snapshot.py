#!/usr/bin/env python3
"""Offline source-byte, manifest-coverage and active-delta replay; not Lean elaboration."""
import hashlib,json,pathlib,sys
base=pathlib.Path(__file__).resolve().parents[1]; p=base/'provenance';bad=[];counts={}
for filename,root in [('source_manifest.json','sources'),('dependency_manifest.json','dependencies'),('comparison_manifest.json','comparison_sources')]:
 m=json.loads((p/filename).read_text());counts[root]=len(m['sources'])
 for f in m['sources']:
  file=base/root/f['path']
  if not file.is_file():bad.append([f['path'],'missing']);continue
  d=file.read_bytes();actual=hashlib.sha1(b'blob '+str(len(d)).encode()+b'\0'+d).hexdigest()
  if actual!=f['sha'] or hashlib.sha256(d).hexdigest()!=f['sha256']:bad.append([f['path'],'hash mismatch'])
current=json.loads((p/'source_manifest.json').read_text())
prefix='Computability/DiophantineConsistency/Lean/'
active={f['path']:f['sha'] for f in json.loads((p/'Lean_tree.json').read_text())['tree'] if f['type']=='blob' and f['path'].endswith('.lean')}
materialized={f['path'][len(prefix):]:f['sha'] for f in current['sources'] if f['path'].startswith(prefix) and f['path'].endswith('.lean')}
if active!=materialized:bad.append(['active Lean coverage','mismatch'])
previous={f['path']:f['sha'] for f in json.loads((p/'previous_Lean_tree.json').read_text())['tree'] if f['type']=='blob' and f['path'].endswith('.lean')}
actual_delta={path:(previous.get(path),active.get(path)) for path in previous.keys()|active.keys() if previous.get(path)!=active.get(path)}
saved_delta={f['path']:(f['old_sha'],f['new_sha']) for f in json.loads((p/'active_tree_delta.json').read_text())['files']}
if actual_delta!=saved_delta:bad.append(['active tree delta','mismatch'])
result={'commit':current['commit'],'checked':counts,'active_Lean_files':len(active),'active_delta_files':len(actual_delta),'failures':bad,'Lean_elaboration':'not run'}
print(json.dumps(result,indent=2));sys.exit(bool(bad))
