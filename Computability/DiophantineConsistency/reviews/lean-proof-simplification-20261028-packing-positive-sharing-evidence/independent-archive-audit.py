import json,hashlib,zipfile,subprocess,re
from pathlib import Path
D=next(Path('Computability/DiophantineConsistency/reviews').glob('*packing-positive-sharing-evidence'));b=json.loads((D/'BUNDLE.json').read_text());h=lambda x:hashlib.sha256(x).hexdigest();Z=D/b['archive'];assert h(Z.read_bytes())==b['archive_sha256']
with zipfile.ZipFile(Z) as z:
 assert z.testzip() is None
 names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(b['members'])
 for n in names:
  data=z.read(n);assert h(data)==b['members'][n]['sha256'] and len(data)==b['members'][n]['bytes']
 print('ZIP CRC, hash, member hashes and sizes:',len(names))
 get=lambda n:z.read(n);rec=lambda n:json.loads(get('prototype/'+n))
 repo='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
 assert subprocess.check_output(['git','rev-parse',b['source_commit']+'^']).decode().strip()==b['source_parent']
 for n in ['CurrentPositiveZero2011','CurrentWitnessEquivalence2011']:
  for phase,ref in [('baseline',b['source_parent']),('final',b['source_commit'])]:
   data=subprocess.check_output(['git','show',ref+':'+repo+n+'.lean']);assert data==get(f'commit/{phase}/{n}.lean')==get(f'prototype/{phase}-commit-{n}.lean')==get(f'snapshots/{phase}/{n}.lean')
 for n in ['ThirteenCarrierSoundness','ThirteenFreshSeed','NativePositiveSourceConstruction']:
  assert get(f'commit/current-provider/{n}.lean')==subprocess.check_output(['git','show',b['source_commit']+':'+repo+n+'.lean'])
 assert get('independent/current-packing-independent-review.txt')==(D/'independent-review.txt').read_bytes();print('commit, parent, providers and independent review verified')
 providers={}
 for r in rec('refresh-records.json'):
  if r['module'] in ['CurrentHaltPacking2011','CurrentSoundness2011']:providers[r['module']]=r
 for r in rec('refresh3-records.json'):
  n=r['module'];assert r['status']==0 and r['before']==r['after']==h(get(f'commit/current-provider/{n}.lean')) and r['log_sha256']==h(get(f'prototype/refresh3-{n}.log')) and r['time'].encode()==get(f'prototype/refresh3-{n}.time')
  for d in r['direct_inputs']:
   assert d['before']==d['after'];n2=d['module'].split('.')[-1]
   if n2 in providers:assert d['before']==providers[n2]['object_sha256'] and d['resolved']==providers[n2]['object']
  providers[n]=r;print('refreshed',n)
 rows={}
 for r in rec('records2.json'):
  n=r['module'];ph=r['phase'];assert r['status']==0 and r['before']==r['after']==h(get(f'snapshots/{ph}/{n}.lean')) and r['log_sha256']==h(get(f'prototype/current2-{ph}-{n}.log')) and r['time'].encode()==get(f'prototype/current2-{ph}-{n}.time')
  for d in r['direct_inputs']:
   assert d['before']==d['after'];m=d['module'].split('.')[-1];p=providers.get(m) or rows[ph,m];assert d['before']==p['object_sha256'] and d['resolved']==p['object']
  rows[ph,n]=r
 assert len(rows)==8
 for n in ['CurrentPositiveZero2011Checks','CurrentWitnessEquivalence2011Checks']:assert rows['baseline',n]['object_sha256']==rows['final',n]['object_sha256']
 print('eight endpoint/check builds and paired client hashes verified')
 for f in ['probe2-records.json','name-probe2-records.json']:
  for p in rec(f):
   assert p['status']==0 and p['source_before']==p['source_after']==h(get('prototype/'+Path(p['source']).name)) and p['log_sha256']==h(get('prototype/'+Path(p['log']).name))
   for o in p['objects']:
    assert o['before']==o['after'];n=Path(o['path']).stem;assert o['before']==rows[p['phase'],n]['object_sha256']
   assert get('prototype/'+Path(p['log']).name)==get('prototype/'+p['phase']+'-'+p['probe']+'.log')
 print('six probes and three name probes verified')
 for n in ['simp','instances']:assert get(f'prototype/current2-baseline-{n}.log')==get(f'prototype/current2-final-{n}.log')
 def parse(phase):
  s=get(f'prototype/current2-{phase}-interfaces.log').decode();return {v.split(' TYPE ',1)[0]:v for v in re.split(r'(?m)^DECL ',s) if v.strip()}
 a,c=parse('baseline'),parse('final');assert len(a)==len(c)==24 and all(a[k]==c[k] for k in a.keys()&c.keys());print('declarations removed',list(a.keys()-c.keys()),'added',list(c.keys()-a.keys()))
 oldblocks=[a[n].split(' TYPE ',1)[1] for n in a.keys()-c.keys()]; new=c['DiophantineConsistency.CurrentPositiveZero2011.packing_positive_zero._proof_1'].split(' TYPE ',1)[1];assert oldblocks[0]==oldblocks[1]==new
 for reg in ['simp','instances']:
  t=get(f'prototype/current2-baseline-{reg}.log').decode();assert all(n not in t for n in a.keys()-c.keys())
 print('removed generated types and axioms equal replacement; absent from simp and instances')
 for r in rec('repeat2-records.json'):
  n=r['module'];ph=r['phase'];assert r['status']==0 and r['before']==r['after']==h(get(f'snapshots/{ph}/{n}.lean')) and r['log_sha256']==h(get('prototype/'+Path(r['log']).name)) and r['time'].encode()==get('prototype/'+Path(r['command'][r['command'].index('-o')+1]).name) and r['object_sha256']==rows[ph,n]['object_sha256']
 print('four repeat records verified')
 sr=rec('search-records.json');assert sr['tracked_lean']['status']==sr['endpoint_files']['status']==1 and sr['endpoint_files']['count']==12 and sr['broad_documents']['status']=='terminated'
 for k in ['tracked_lean','endpoint_files']:assert h(get('prototype/'+sr[k]['log']))==sr[k]['sha256']
 for f in ['refresh2-records.json','setup-failure-records2.json']:assert rec(f)[0]['status']!=0
 print('failed attempts and scoped searches verified')
 root=json.loads(get('provider/native-ordinary-ROOT.json'));assert root['status']=='PASS';lookup={x['module']:x for x in root['selected_custom']}
 matches=0
 for r in rec('refresh3-records.json'):
  for d in r['direct_inputs']:
   n=d['module'];short=n.split('.')[-1]
   if short in ['ThirteenCarrierSoundness','ThirteenFreshSeed','SignedPellResidue']:continue
   q=lookup[n];src=('Computability/HilbertTenthProblem/Lean/' if n.startswith('Diophantine.Paper') else 'Computability/DiophantineConsistency/Lean/')+n.replace('.','/')+'.lean';sh=h(subprocess.check_output(['git','show',b['source_commit']+':'+src]));assert q['source']['sha256']==sh and q['object']['sha256']==d['before'];matches+=1
 print('fresh upstream ROOT source/object matches',matches);assert matches==6
 matches=0;mismatches=[]
 for r in rec('refresh-records.json'):
  for d in r['direct_inputs']:
   n=d['module'];q=lookup[n];src=repo+n.split('.')[-1]+'.lean';sh=h(subprocess.check_output(['git','show',b['source_parent']+':'+src]));match=q['source']['sha256']==sh and q['object']['sha256']==d['before']
   if match:matches+=1
   else:mismatches.append(n)
 print('original replay ROOT matches',matches,'unmatched',mismatches);assert matches==9 and mismatches==['DiophantineConsistency.ThirteenFreshSeed']
 man=rec('prior-reused-provider-manifest.json');p=repo+'SignedPellResidue.lean';old=man['protected'][p];entry=next(x for x in man['reused_objects'] if x['source']==p);d=next(x for x in providers['ThirteenCarrierSoundness']['direct_inputs'] if x['module'].endswith('.SignedPellResidue'));assert entry['sha256']==d['before'] and old==h(subprocess.check_output(['git','show','16ea41285c^:'+p]));current=h(subprocess.check_output(['git','show',b['source_commit']+':'+p]));assert old!=current;print('old SignedPell boundary old/current/object',old,current,d['before'])
 print('objects excluded: validation uses retained receipts, not archived object bytes')
