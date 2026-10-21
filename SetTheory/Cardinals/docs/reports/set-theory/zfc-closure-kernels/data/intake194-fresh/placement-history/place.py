from pathlib import Path, PurePosixPath
import json, subprocess, zipfile, stat
repo=Path.cwd()
p=json.loads(Path('/tmp/zfc-intake194/procedure/placement-plan.json').read_text())
fresh=Path('/tmp/zfc-intake194/placement-fresh2'); fresh.mkdir(exist_ok=False)
new=[]; n=0
for s in p['sources']:
 archive=repo/s['archive']
 assert subprocess.check_output(['git','rev-parse',s['arrival']+':'+s['archive']],text=True).strip()==s['archive_blob']
 assert subprocess.check_output(['git','hash-object',str(archive)],text=True).strip()==s['archive_blob']
 dest=fresh/str(s['source']); dest.mkdir()
 with zipfile.ZipFile(archive) as z:
  entries={i.filename:i for i in z.infolist() if not i.is_dir()}
  assert set(entries)=={m['member'] for m in s['members']}
  for m in s['members']:
   rel=PurePosixPath(m['member']); info=entries[m['member']]
   assert not rel.is_absolute() and '..' not in rel.parts and not stat.S_ISLNK(info.external_attr>>16)
   data=z.read(info); fp=dest/rel; fp.parent.mkdir(parents=True,exist_ok=True); fp.write_bytes(data)
   assert subprocess.check_output(['git','hash-object','--stdin'],input=data).decode().strip()==m['blob']
   if m['role']=='new':
    target=repo/m['target']; assert not target.exists() or target.read_bytes()==data; target.parent.mkdir(parents=True,exist_ok=True); target.write_bytes(data); new.append(m['target'])
   elif m['role'] in ('existing-alias','batch-alias'):
    if m['role']=='batch-alias': assert (repo/m['target']).read_bytes()==data
    if m['role']=='existing-alias':
     assert subprocess.check_output(['git','show',m['current_ref']+':'+m['target']])==data
     subprocess.run(['git','diff','--quiet',m['current_ref'],'--',m['target']],check=True)
     h=m['original_introduction']; assert subprocess.check_output(['git','rev-parse',h['commit']+':'+h['path']],text=True).strip()==m['blob']
   elif m['role']=='history-alias':
    h=m['history']; assert subprocess.check_output(['git','show',h['commit']+':'+h['path']])==data
   else: assert m['role']=='archive-only'
   n+=1
p['status']='PLACED_FROM_FRESH_EXTRACTION'
p['verification']={'members':n,'new_files':len(new),'all_member_blobs_checked':True,'all_aliases_checked':True,'checksum_manifest_validation':False}
p['notes'][0]='Placed from a fresh extraction separate from all execution copies; all member blobs and aliases checked.'
map_path=p['host']+'/data/intake194-placement.json'; (repo/map_path).write_text(json.dumps(p,indent=2)+'\n'); new.append(map_path)
subprocess.run(['git','add','-f','--',*new],check=True)
for s in p['sources']:
 for m in s['members']:
  if m['role']=='new':
   data=(fresh/str(s['source'])/m['member']).read_bytes()
   expected=subprocess.check_output(['git','hash-object','--path='+m['target'],'--stdin'],input=data).decode().strip()
   staged=subprocess.check_output(['git','rev-parse',':'+m['target']],text=True).strip()
   assert staged==expected
   m['placed_blob']=staged
(repo/map_path).write_text(json.dumps(p,indent=2)+'\n')
subprocess.run(['git','add','--',map_path],check=True)
subprocess.run(['git','rm','--',*[s['archive'] for s in p['sources']]],check=True)
Path('/tmp/zfc-intake194/placement-paths.json').write_text(json.dumps(new))
print('PASS:',n,'members;',len(new)-1,'new payloads; mapped aliases checked;one ZIP retired')
