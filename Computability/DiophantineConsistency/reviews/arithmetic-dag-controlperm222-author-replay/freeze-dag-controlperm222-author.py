from pathlib import Path
import hashlib,json,shutil,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');D=R/'Computability/DiophantineConsistency';REV=D/'reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
paths=[Path(x)for x in json.loads(Path('/tmp/dag-controlperm222-controller-author-attempts.json').read_text())]
states=[json.loads((p/'AUTHOR.json').read_text())for p in paths]
assert states[-1]['status']=='PASS'
records=[r for st in states for r in st['records']if r['module']=='BusyBeaver.ZFC.PackedTables'and r['exit_code']==0]+states[-1]['records']
assert len(records)==3
for row in records:
 assert row['exit_code']==0
 for key in ['source','snapshot','object','log','timing']:assert sha(row[key]['path'])==row[key]['sha256'],row[key]['path']
 assert Path(row['object']['path']).is_file()and not Path(row['object']['path']).is_symlink()
assert sum(len(r['axiom_reports'])for r in records)==12
out=REV/'arithmetic-dag-controlperm222-author-replay';assert not out.exists();out.mkdir()
observations=0
for ix,(p,st)in enumerate(zip(paths,states),1):
 target=out/f'attempt{ix}';target.mkdir()
 for name in ['AUTHOR.json','inputs.json']:
  shutil.copyfile(p/name,target/name)
 inp=json.loads((p/'inputs.json').read_text())
 for pin in inp['pins']:
  assert sha(pin['path'])==pin['sha256'],pin['path'];observations+=1
 for row in st['records']:
  assert sha(row['snapshot']['path'])==row['source']['sha256']
  for key in ['snapshot','object','log','timing']:
   if key in row:
    f=Path(row[key]['path']);assert sha(f)==row[key]['sha256'];shutil.copyfile(f,target/f.name)
for f in ['/tmp/arithmetic-dag-controlperm222-controller-author.py','/tmp/arithmetic-dag-controlperm222-controller-author-v2.py','/tmp/arithmetic-dag-controlperm222-controller-author-v3.py','/tmp/build-dag-controlperm222-source.py','/tmp/chunk-dag-controlperm222-source.py','/tmp/index-dag-controlperm222-source.py','/tmp/c222-dagperm-table-plan-audit.py','/tmp/dag-controlperm222-packed-audit-attempt3.json','/tmp/dag-controlperm222-packed-audit-attempt4.json','/tmp/dag-controlperm222-packed-audit-final.json','/tmp/dag-controlperm222-generic-prefix.py','/tmp/dag-controlperm222-generic-prefix-v2.py',__file__]:
 shutil.copyfile(f,out/Path(f).name)
packet=dict(status='PASS',scope='Actual fixed4751-row catalogue and unconditional root occurrence, plus represented internal run and conditional structured-exit adapters. No EnumStep/p215/source-ZFC/HA equivalence.',counts=states[-1]['counts'],records=records,attempts=[rec(out/f'attempt{i}'/'AUTHOR.json')for i in range(1,len(paths)+1)],final_inputs=rec(out/f'attempt{len(paths)}'/'inputs.json'),all_prior_pin_reauthentication_observations=observations,final_private=str(paths[-1]),provider_note='Independent DagLoops peer objects selected per root direction in an explicit supplement, preserving the earlier plan and provider records.',driver=rec(out/Path(states[-1]['driver']['path']).name))
late=[REV/'arithmetic-dag-loops-root.md',REV/'arithmetic-dag-loops-root-authentication/arithmetic-dag-loops-root-authentication.json']
packet['later_accepted_provider_supplement']={'root_commit':'b5459f3024','records':[rec(f) for f in late],'scope':'Root acceptance arrived during attempt3; source/object pins unchanged. Earlier inputs retain their actual pending status.'}
for f in late:shutil.copyfile(f,out/f.name)
prefixes=[]
for ix,name in enumerate(['5czahtux','22gri4no','fc3lxcda'],1):
 prefix=Path('/tmp/dag-controlperm222-generic-prefix-'+name);meta=json.loads((prefix/'PREFIX.json').read_text())
 target=out/f'generic-prefix{ix}';target.mkdir()
 assert sha(meta['snapshot']['path'])==meta['full_source']['sha256']
 for key in ['source','snapshot','log','timing','object']:
  if key in meta:
   r=meta[key];assert sha(r['path'])==r['sha256'];shutil.copyfile(r['path'],target/Path(r['path']).name)
 shutil.copyfile(prefix/'PREFIX.json',target/'PREFIX.json');prefixes.append(rec(target/'PREFIX.json'))
packet['diagnostic_prefixes']=prefixes
packet['diagnostic_prefix_scope']='Exact generic source prefix only, no endpoint claimed and no prefix object is imported by the final module.'
packetpath=REV/'arithmetic-dag-controlperm222-replay.json';assert not packetpath.exists();save(packetpath,packet)
manifest=[dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size)for p in sorted(out.rglob('*'))if p.is_file()]
save(out/'FILES.json',manifest)
for p in [packetpath,out/'FILES.json']:print(sha(p),p)
print('evidence_files',len(manifest),'observations',observations)
