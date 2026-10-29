from pathlib import Path
import hashlib,json,zipfile,subprocess
D=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-variation-tail-sharing-evidence');m=json.loads((D/'BUNDLE.json').read_text());A=D/m['archive'];sh=lambda b:hashlib.sha256(b).hexdigest();assert sh(A.read_bytes())==m['archive_sha256'];assert subprocess.check_output(['git','rev-parse',m['source_commit']+'^'],text=True).strip()==m['source_parent']
with zipfile.ZipFile(A) as z:
 assert z.testzip() is None;names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(m['members']);assert not any(n.endswith('.olean') for n in names)
 for n in names:
  b=z.read(n);v=m['members'][n];assert len(b)==v['bytes'] and sh(b)==v['sha256'],n
 print('ARCHIVE CRC SHA-256',m['archive_sha256'],'MEMBERS',len(names),'PASS')
 def read(n):return z.read(n)
 def j(n):return json.loads(read(n))
 def git(path,ref=None):return subprocess.check_output(['git','show',(ref or m['source_parent'])+':'+path])
 root='Computability/DiophantineConsistency/Lean/DiophantineConsistency/';target='ArithmeticConstructionVariation'
 for phase,ref in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  b=git(root+target+'.lean',ref);assert b==read('commit/'+phase+'.lean')==read('prototype/'+phase+'-commit.lean')==read('snapshots/sources/refreshed2-'+phase+'/DiophantineConsistency/'+target+'.lean');print('GIT',phase,sh(b))
 assert read('independent/variation-tail-independent-review.txt')==(D/'independent-review.txt').read_bytes();print('REVIEW',sh(read('independent/variation-tail-independent-review.txt')))
 for n in names:
  if n.startswith('provider/'):
   live=Path('/'+n[len('provider/'):]);b=read(n)
   if live.exists():assert sh(live.read_bytes())==sh(b);print('PRIOR RECEIPT',n,sh(b),'live matched')
   else:print('PRIOR RECEIPT',n,sh(b),'live unavailable')
 def checkrecord(x):
  assert x['status']==0 and x['source_before']==x['source_after'];snap='snapshots/'+x['source'].split('/tmp/variation-tail-sharing/',1)[1];assert sh(read(snap))==x['source_before'],snap
  assert x['workspace_before']==x['workspace_after']==sh(git(x['workspace']))
  if x['module']!=target:assert x['source_before']==x['workspace_before']
  assert sh(read('prototype/'+Path(x['log']).name))==x['log_sha256'];assert sh(read('prototype/'+Path(x['time']).name))==x['time_sha256'];assert read('prototype/'+Path(x['time']).name).decode().strip()==x['timing'].strip()
  for d in x['direct_inputs']:
   assert d['object_before']==d['object_after']
   if d.get('source'):
    assert d['source_before']==d['source_after']==sh(git(d['source']))
  print('BUILD',x['phase'],x['module'],x['timing'].strip(),x['object_sha256'])
 # Only the ConstructionUnit from the first refresh is reused; its PackingCells is historical.
 unit=next(x for x in j('prototype/refreshed-common-records.json') if x['module']=='ArithmeticConstructionUnit');pack=j('prototype/refreshed2-common-records.json')[0];checkrecord(unit);checkrecord(pack)
 phase_targets={}
 for ph in ('baseline','final'):
  rs=j('prototype/refreshed2-'+ph+'-records.json');assert len(rs)==2
  for x in rs:checkrecord(x)
  t=next(x for x in rs if x['module']==target);c=next(x for x in rs if x['module']=='ArithmeticConstructionAssembly');phase_targets[ph]=t['object_sha256'];ds={d['module'].split('.')[-1]:d for d in c['direct_inputs']};assert ds[target]['object_before']==t['object_sha256'];assert ds['ArithmeticPackingCells']['object_before']==pack['object_sha256'];assert ds['ArithmeticConstructionUnit']['object_before']==unit['object_sha256'];assert ds[target]['source_before']==sh(git(root+target+'.lean'))
  print('ASSEMBLY',ph,c['object_sha256'])
 assert j('prototype/refreshed2-baseline-records.json')[1]['object_sha256']==j('prototype/refreshed2-final-records.json')[1]['object_sha256']
 for ph in ('baseline','final'):
  for x in j('prototype/refreshed2-'+ph+'-probes.json'):
   assert x['status']==0 and x['source_before']==x['source_after']==sh(read('prototype/'+Path(x['source']).name));assert x['object_before']==x['object_after']==phase_targets[ph];assert x['log_sha256']==sh(read('prototype/'+Path(x['log']).name));assert x['time_sha256']==sh(read('prototype/'+Path(x['time']).name))
 for kind in ('interfaces','simp','instances'):
  a=read('prototype/refreshed2-baseline-'+kind+'.log');b=read('prototype/refreshed2-final-'+kind+'.log');assert a==b;print('PROBE',kind,'lines',len(a.splitlines()))
 assert len(read('prototype/refreshed2-baseline-simp.log').splitlines())==38804 and len(read('prototype/refreshed2-baseline-instances.log').splitlines())==16567
 assert sum(x.startswith(b'DECL ') for x in read('prototype/refreshed2-baseline-interfaces.log').splitlines())==6
 mappings=j('prototype/refreshed2-provider-matches.json')
 checkbuilds=[unit,pack]+j('prototype/refreshed2-baseline-records.json')+j('prototype/refreshed2-final-records.json')
 for x in mappings:
  owner=next(y for y in checkbuilds if y['phase']==x['phase'] and y['module']==x['client'])
  edge=next(d for d in owner['direct_inputs'] if d['module'].split('.')[-1]==x['module'])
  assert edge['source_before']==x['source'] and edge['object_before']==x['object']
  if x['module']==target:
   ph=x['phase'].split('-')[-1];assert x['object']==phase_targets[ph] and x['source']==sh(git(root+target+'.lean'));continue
  for p in x['matches']:
   name='prototype/'+Path(p).name if p.startswith('/tmp/variation-tail-sharing/') else 'provider/'+p.lstrip('/')
   assert name in names,(x['module'],name)
   v=j(name);vs=v if isinstance(v,list) else list(v.values());ok=False
   for a in vs:
    if not isinstance(a,dict) or a.get('module','').split('.')[-1]!=x['module']:continue
    src=a.get('source_sha256') or a.get('source_before') or a.get('before') or a.get('source');obj=a.get('object_sha256') or a.get('object')
    if src==x['source'] and obj==x['object'] and a.get('status',0)==0:ok=True
   assert ok,(x['module'],name)
 print('PROVIDER MAPPINGS',len(mappings),'linked to archived prior/source-build records')
 for x in j('prototype/cached-boundaries.json'):
  assert x['current_source_sha256']==sh(git(x['current_source']));p=Path(x['object']);
  if p.is_file():assert sh(p.read_bytes())==x['object_sha256'];print('CACHED BOUNDARY',x['module'],x['object_sha256'],'live matched')
  else:print('CACHED BOUNDARY',x['module'],x['object_sha256'],'live unavailable')
 failed=j('prototype/initial-failed-records.json')[0];assert failed['status']!=0 and failed['source_before']==failed['source_after']==sh(read('commit/baseline.lean')) and failed['log_sha256']==sh(read('prototype/initial-failed.log')) and failed['time_sha256']==sh(read('prototype/initial-failed.time'));print('INITIAL overlay failure log/time preserved under new names')
 oldpack=next(x for x in j('prototype/refreshed-common-records.json') if x['module']=='ArithmeticPackingCells');oldplane=next(d for d in oldpack['direct_inputs'] if d['module'].endswith('ArithmeticWangPlane'));newplane=next(d for d in pack['direct_inputs'] if d['module'].endswith('ArithmeticWangPlane'));assert oldplane['object_before']!=newplane['object_before'];assert b'Command terminated by signal' in read('prototype/interrupted-refreshed-baseline.time');print('REFRESH historical WangPlane differs; interrupted baseline recorded')
 print('SCOPE: no .olean binaries in ZIP; archived hashes verify receipt links, not independently reconstructed objects. Wider transitive closure is cached.')
