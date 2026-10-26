#!/usr/bin/env python3
import pathlib,json,hashlib,shutil
BASE=pathlib.Path(__file__).resolve().parents[1]; OLD=BASE.parent/'lean_simplification_round2_20261026/sources'; P=BASE/'provenance'; HEAD='22e020937caa81d0cb72a4f63071d6c0bcc1eba9'
root=json.load(open(P/'root_tree.json'))['tree']; target=json.load(open(P/'target_root_tree.json'))['tree']; selected=[]; prefix='Computability/DiophantineConsistency/'
for group in ['Lean','reviews','scripts','tools']:
 for f in json.load(open(P/(group+'_tree.json')))['tree']:
  p=f['path']
  if f['type']=='blob' and (group=='Lean' or group=='scripts' or (group=='tools' and p.startswith('generate_')) or (group=='reviews' and 'lean' in p.lower() and p.endswith('.md'))):selected.append({**f,'path':prefix+group+'/'+p})
for f in target:
 if f['type']=='blob' and f['path'].endswith('.md'):selected.append({**f,'path':prefix+f['path']})
for f in root:
 if f['type']=='blob' and f['path'] in ['lakefile.toml','lake-manifest.json','lean-toolchain','README.md','LICENSE','.gitmodules','ProveIt.lean']:selected.append(f)
# Include all newly changed review docs, not only ones whose names contain Lean.
selected_by={f['path']:f for f in selected}
reviews={prefix+'reviews/'+f['path']:{**f,'path':prefix+'reviews/'+f['path']} for f in json.load(open(P/'reviews_tree.json'))['tree'] if f['type']=='blob'}
for f in json.load(open(P/'compare_summary.json'))['files']:
 if f['filename'] in reviews:selected_by[f['filename']]=reviews[f['filename']]
selected=sorted(selected_by.values(),key=lambda f:f['path']); pending=[]; verified=[]
for f in selected:
 src=OLD/f['path']; dst=BASE/'sources'/f['path']; f['source_url']='https://github.com/VladimirReshetnikov/ProveIt/blob/'+HEAD+'/'+f['path']
 if src.is_file():
  data=src.read_bytes(); sha=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
  if sha==f['sha']:
   dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data);f.update(sha256=hashlib.sha256(data).hexdigest(),verified=True,retrieval='verified identical old snapshot bytes');verified.append(f);continue
 pending.append(f)
(P/'selected_manifest.json').write_text(json.dumps(selected,indent=2)+'\n');(P/'pending.json').write_text(json.dumps(pending,indent=2)+'\n');(P/'reused_manifest.json').write_text(json.dumps(verified,indent=2)+'\n')
print(json.dumps({'selected':len(selected),'verified_reused':len(verified),'pending':len(pending),'pending_paths':[f['path'] for f in pending]},indent=2))
