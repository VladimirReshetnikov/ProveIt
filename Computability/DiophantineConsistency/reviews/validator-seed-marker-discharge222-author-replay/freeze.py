from pathlib import Path
import hashlib,json,shutil
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=R/'Computability/DiophantineConsistency'
O=D/'reviews/validator-seed-marker-discharge222-author-replay'
F=D/'reviews/validator-seed-marker-discharge222-replay.json'
names=['aeuz4ng3','2c4cke0x','oiu3_yke','7dh_s5ez','j4ujj45x','4a3d0uc9','j_zbsg02','sxblo95d']
def rec(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def save(p,x):Path(p).write_text(json.dumps(x,indent=2)+'\n')
def need(x,m):
 if not x:raise RuntimeError(m)
pins={};observations=0
def check(x):
 global observations
 a=rec(x['path']);need(a['sha256']==x['sha256'],'hash '+x['path']);pins[a['path']]=a;observations+=1;return a
need(not O.exists()and not F.exists(),'fresh author freeze')
need(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
attempts=[]
for number,name in enumerate(names,1):
 p=Path('/tmp/validator-seed-marker-discharge222-author-'+name)
 state=json.loads((p/'AUTHOR.json').read_text());need(state['status']in ['PASS','FAILED'],'terminal attempt')
 inputs=json.loads((p/'inputs.json').read_text())
 for x in inputs['pins']:check(x)
 for x in inputs['sources']:
  check(x['snapshot']);need(x['sha256']==x['snapshot']['sha256'],'preserved source')
 for row in state['records']:
  for k in ['snapshot','log','timing']:check(row[k])
  if 'object'in row:check(row['object'])
 extras=[]
 for x in inputs['sources']:
  obj=p/'lib'/Path(*x['module'].split('.')).with_suffix('.olean')
  if obj.is_file()and not any(r.get('object',{}).get('path')==str(obj)for r in state['records']):extras.append(check(rec(obj)))
 attempts.append(dict(number=number,private=str(p),state=check(rec(p/'AUTHOR.json')),status=state['status'],records=state['records'],available_unrecorded_outputs=extras))
final=attempts[-1];need(final['status']=='PASS'and len(final['records'])==2,'final full pair PASS')
for row in final['records']:
 for k in ['source','snapshot','object','log','timing']:check(row[k])
 need(row['exit_code']==0,'final compiler success')
need([len(r['axiom_reports'])for r in final['records']]==[0,14],'fourteen final reports')
for x in list(pins.values()):check(x)
O.mkdir()
for attempt in attempts:
 p=Path(attempt['private']);target=O/('attempt-'+str(attempt['number']).zfill(2));target.mkdir()
 for name in ['AUTHOR.json','inputs.json','driver.py','ValidatorSeedMarkerDischarge222.lean','ValidatorSeedMarkerDischarge222Checks.lean','ValidatorSeedMarkerDischarge222.log','ValidatorSeedMarkerDischarge222.time','ValidatorSeedMarkerDischarge222Checks.log','ValidatorSeedMarkerDischarge222Checks.time']:
  if(p/name).is_file():shutil.copyfile(p/name,target/name)
for name,p in [('inventory-audit-v1.log',Path('/tmp/marker-discharge-inventory-attempt2-d04iowy3/audit.log')),('inventory-audit-final.log',Path('/tmp/marker-discharge-inventory-attempt3-4ajgncei/audit.log'))]:shutil.copyfile(p,O/name)
shutil.copyfile(__file__,O/'freeze.py')
save(O/'reauthentication.json',dict(status='PASS',observations=observations,unique_paths=len(pins),pins=list(pins.values()),qualification='Historical mutable leaf paths authenticated through both preserved snapshots. Attempt7 compiled both leaves but its report-count audit rejected an ambiguous print. Its otherwise unrecorded Checks object is retained as an available output, not a successful packet.'))
packet=dict(status='PASS',scope='ROOT-authored conditional marker/domain discharge; independent review pending.',counts=dict(cached=202,Foundation=136,artifacts=610,boundaries=45,providers=655,refresh=0),attempts=attempts,final=final,
 plan=rec(D/'research/validator-seed-marker-discharge-cache-plan.json'),plan_manifest=rec(D/'research/validator-seed-marker-discharge-plan-FILES.json'),reauthentication=rec(O/'reauthentication.json'),freeze=rec(O/'freeze.py'))
save(F,packet)
files=sorted(p for p in O.rglob('*')if p.is_file())+[F]
save(O/'FILES.json',[dict(rec(p),path=str(p.relative_to(R)))for p in files])
print(json.dumps(dict(packet=rec(F),manifest=rec(O/'FILES.json'),files=len(files),observations=observations,unique_paths=len(pins)),indent=2))
