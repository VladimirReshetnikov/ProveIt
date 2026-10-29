from pathlib import Path
import hashlib,json,zipfile,subprocess
D=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-controller-stride-period-evidence');m=json.loads((D/'BUNDLE.json').read_text());A=D/m['archive'];sh=lambda b:hashlib.sha256(b).hexdigest();assert sh(A.read_bytes())==m['archive_sha256'];assert subprocess.check_output(['git','rev-parse',m['source_commit']+'^'],text=True).strip()==m['source_parent']
with zipfile.ZipFile(A) as z:
 assert z.testzip() is None;names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(m['members']);assert not any(n.endswith('.olean') for n in names)
 for n in names:
  b=z.read(n);x=m['members'][n];assert len(b)==x['bytes'] and sh(b)==x['sha256'],n
 print('ARCHIVE CRC SHA-256',m['archive_sha256'],'MEMBERS',len(names),'PASS')
 def read(n):return z.read(n)
 def j(n):return json.loads(read(n))
 def git(path,ref=None):return subprocess.check_output(['git','show',(ref or m['source_parent'])+':'+path])
 root='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
 for phase,ref in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  b=git(root+'ArithmeticControllerStride.lean',ref);assert b==read('commit/'+phase+'.lean')==read('prototype/'+('baseline' if phase=='baseline' else 'variant2')+'-commit.lean')==read('snapshots/'+('baseline' if phase=='baseline' else 'variant2')+'/DiophantineConsistency/ArithmeticControllerStride.lean');print('GIT',phase,sh(b))
 assert read('independent/controller-stride-independent-review.txt')==(D/'independent-review.txt').read_bytes();print('REVIEW',sh(read('independent/controller-stride-independent-review.txt')))
 prior={'provider/origin-block-sharing/records.json':'/tmp/origin-block-sharing/records.json','provider/outer-seed-bound-sharing/assembly-builds2.json':'/tmp/outer-seed-bound-sharing/assembly-builds2.json','provider/dag-independent-audit/fol-refresh-records.json':'/tmp/dag-independent-audit/fol-refresh-records.json'}
 for n,p in prior.items():
  b=read(n);q=Path(p)
  if q.exists():assert sh(b)==sh(q.read_bytes());print('PRIOR RECEIPT',n,sh(b),'live copy matched')
  else:print('PRIOR RECEIPT',n,sh(b),'live copy unavailable')
 origin=j('provider/origin-block-sharing/records.json');packing=next(x for x in origin if x['phase']=='final' and x['module']=='ArithmeticPackingBlocks' and x['status']==0);data=next(x for x in origin if x['phase']=='final' and x['module']=='ArithmeticControllerData' and x['status']==0)
 assert packing['source_before']==packing['source_after']==sh(git(root+'ArithmeticPackingBlocks.lean'));assert data['source_before']==data['source_after']==sh(git(root+'ArithmeticControllerData.lean'))
 d=data['inputs']['DiophantineConsistency.ArithmeticPackingBlocks'];assert d['object_before']==d['object_after']==packing['object_sha256'];assert d['source_before']==d['source_after']!=packing['source_before'];print('PACKING prior input source sample is historical',d['source_before'],'final object built from',packing['source_before'])
 cyc=next(x for x in j('provider/outer-seed-bound-sharing/assembly-builds2.json') if x['module'].endswith('ArithmeticCyclicWord') and x['status']==0);di=packing['inputs']['DiophantineConsistency.ArithmeticCyclicWord'];assert cyc['source_sha256']==di['source_before']==di['source_after']==sh(git(root+'ArithmeticCyclicWord.lean'));assert cyc['object_sha256']==di['object_before']==di['object_after']
 cantor=next(x for x in j('provider/dag-independent-audit/fol-refresh-records.json') if x['module']=='BusyBeaver.ZFC.ArithmeticCantor' and x['status']==0);assert cantor['source_sha256']==cantor['source_after']==sh(git('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCantor.lean'))
 common=j('prototype/common-records.json')[0];assert common['status']==0 and common['before']==common['after']==sh(read('snapshots/common/DiophantineConsistency/ArithmeticControllerChoice.lean'))==sh(git(root+'ArithmeticControllerChoice.lean'));ci={x['module'].split('.')[-1]:x for x in common['direct_inputs']};assert ci['ArithmeticControllerData']['before']==ci['ArithmeticControllerData']['after']==data['object_sha256'];assert ci['ArithmeticCantor']['before']==ci['ArithmeticCantor']['after']==cantor['object_sha256'];assert sh(read('prototype/'+Path(common['log']).name))==common['log_sha256'];assert read('prototype/'+Path(common['command'][common['command'].index('-o')+1]).name).decode()==common['time'];print('PROJECT PROVIDER RECORD LINKS PASS')
 controller=git(root+'ArithmeticController.lean');assert controller==read('snapshots/baseline/DiophantineConsistency/ArithmeticController.lean')==read('snapshots/variant2/DiophantineConsistency/ArithmeticController.lean')
 target={}
 for phase in ('baseline','variant2'):
  recs=j('prototype/'+phase+'-records.json');assert len(recs)==2
  for x in recs:
   assert x['status']==0 and x['before']==x['after'];source=read('snapshots/'+phase+'/DiophantineConsistency/'+x['module']+'.lean');assert sh(source)==x['before'];assert sh(read('prototype/'+Path(x['log']).name))==x['log_sha256'];assert read('prototype/'+Path(x['command'][x['command'].index('-o')+1]).name).decode()==x['time'];
   for d in x['direct_inputs']:assert d['before']==d['after']
  t=next(x for x in recs if x['module']=='ArithmeticControllerStride');c=next(x for x in recs if x['module']=='ArithmeticController');target[phase]=t['object_sha256'];di={d['module'].split('.')[-1]:d['before'] for d in t['direct_inputs']};assert di['ArithmeticControllerData']==data['object_sha256'];di={d['module'].split('.')[-1]:d['before'] for d in c['direct_inputs']};assert di['ArithmeticControllerStride']==t['object_sha256'] and di['ArithmeticControllerChoice']==common['object_sha256'];print('BUILDS',phase,'target',t['time'].strip(),'client object',c['object_sha256'])
 assert j('prototype/baseline-records.json')[1]['object_sha256']==j('prototype/variant2-records.json')[1]['object_sha256']
 for kind in ('names','interfaces','simp','instances'):
  for phase in ('baseline','variant2'):
   p=j('prototype/probe-'+kind+'-'+phase+'.json');assert p['status']==0 and p['source_before']==p['source_after']==sh(read('prototype/'+Path(p['source']).name));assert p['object_before']==p['object_after']==target[phase];assert p['log_sha256']==sh(read('prototype/'+Path(p['log']).name))
  a=read('prototype/baseline-'+kind+'.log');b=read('prototype/variant2-'+kind+'.log');assert a==b;print('PROBE',kind,'lines',len(a.splitlines()))
 assert len(read('prototype/baseline-simp.log').splitlines())==38766 and len(read('prototype/baseline-instances.log').splitlines())==16545
 for ph in ('baseline-r1','variant2-r1','baseline-r2','variant2-r2'):
  x=j('prototype/'+ph+'-records.json')[0];assert x['status']==0 and x['before']==x['after'] and x['object_sha256']==target[ph.split('-')[0]];assert sh(read('prototype/'+Path(x['log']).name))==x['log_sha256'];assert read('prototype/'+Path(x['command'][x['command'].index('-o')+1]).name).decode()==x['time'];print('REPEAT',ph,x['time'].strip())
 f=j('prototype/failed-initial-records.json')[0];assert f['status']!=0 and f['before']==f['after']==sh(read('prototype/failed-initial.lean')) and f['log_sha256']==sh(read('prototype/failed-initial.log')) and read('prototype/failed-initial.time').decode()==f['time'];print('FAILED INITIAL preserved')
 old=j('prototype/variant2-initial-target-records.json')[0];assert old['status']==0 and old['before']==old['after']==sh(read('commit/final.lean')) and old['object_sha256']==target['variant2'] and old['log_sha256']==sh(read('prototype/variant2-ArithmeticControllerStride.log'));assert old['time']!=read('prototype/variant2-ArithmeticControllerStride.time').decode();print('INITIAL variant2 time overwritten as documented')
 prior=j('prototype/final-records.json')[0];assert prior['status']==0 and prior['before']==prior['after']==sh(read('snapshots/final/DiophantineConsistency/ArithmeticControllerStride.lean'));assert prior['log_sha256']==sh(read('prototype/final-ArithmeticControllerStride.log')) and prior['time']==read('prototype/final-ArithmeticControllerStride.time').decode();print('SUPERSEDED successful periodicity-only candidate verified')
 print('SCOPE: no compiled objects in ZIP; receipt links and source hashes do not reproduce object binaries; transitive inputs cached.')
