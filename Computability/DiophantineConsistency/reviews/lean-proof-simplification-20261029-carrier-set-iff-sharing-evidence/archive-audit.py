from pathlib import Path
import json,hashlib,subprocess,zipfile
D=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261029-carrier-set-iff-sharing-evidence');m=json.loads((D/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();archive=D/m['archive'];assert h(archive.read_bytes())==m['archive_sha256'];print('archive',h(archive.read_bytes()),'manifest',h((D/'BUNDLE.json').read_bytes()))
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None;names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(m['members'])
 for n,v in m['members'].items():
  x=z.read(n);assert len(x)==v['bytes'] and h(x)==v['sha256'],n
 print('CRC, complete member set, hashes/sizes pass',len(names))
 def b(n):return z.read(n)
 def j(n):return json.loads(b(n))
 assert h(b('independent/carrier-set-iff-independent-review.txt'))==m['independent_review']['sha256']==h((D/m['independent_review']['file']).read_bytes());print('independent review hashes match')
 base='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
 target='CurrentCarrierArithmetic2011';clients=['CurrentCarrierArithmetic2011Checks','CurrentHighDigits2011','CurrentSparseDigits2011']
 for ph,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  for mod in [target,*clients]:
   src=b('snapshots/'+ph+'/DiophantineConsistency/'+mod+'.lean');assert src==subprocess.check_output(['git','show',rev+':'+base+mod+'.lean']);
   if mod==target:assert src==b('commit/'+ph+'.lean')
  print('target/client snapshots match',ph,rev)
 providers={}
 for f,prefix in [('provider2-records.json','provider2'),('provider3-records.json','provider3')]:
  for x in j('prototype/'+f):
   n=x['module'];assert x['status']==0 and x['before']==x['after']==h(b('providers/current/'+n+'.lean'));assert b('providers/current/'+n+'.lean')==subprocess.check_output(['git','show',m['source_commit']+':'+base+n+'.lean']);assert x['log_sha256']==h(b('prototype/'+prefix+'-'+n+'.log')) and x['time']==b('prototype/'+prefix+'-'+n+'.time').decode();assert all(d['before']==d['after'] for d in x['direct_inputs']);providers[n]=x;print('fresh provider receipt',n,x['object_sha256'])

 for x in providers['CurrentMasks2011']['direct_inputs']:
  if x['module'].endswith('.CurrentMaskData2011'):assert x['before']==providers['CurrentMaskData2011']['object_sha256']
 prior=j('prototype/refresh3-records.json');seed=next(x for x in prior if x['module']=='ThirteenFreshSeed');carrier=providers['ThirteenCarrierComplete'];assert seed['status']==0 and seed['before']==seed['after']==h(b('providers/current/ThirteenFreshSeed.lean'));assert b('providers/current/ThirteenFreshSeed.lean')==subprocess.check_output(['git','show',m['source_commit']+':'+base+'ThirteenFreshSeed.lean']);assert next(d for d in carrier['direct_inputs'] if d['module'].endswith('.ThirteenFreshSeed'))['before']==seed['object_sha256'];print('prior ThirteenFreshSeed receipt matches fresh provider chain')
 for x in j('prototype/provider-records.json'):
  assert x['module']=='CurrentMasks2011' and x['status']!=0 and x['object_sha256'] is None and x['before']==x['after']==h(b('providers/current/CurrentMasks2011.lean'));assert x['log_sha256']==h(b('prototype/provider-CurrentMasks2011.log')) and x['time']==b('prototype/provider-CurrentMasks2011.time').decode();assert b'lowSupport_range_Ico_disjoint' in b('prototype/provider-CurrentMasks2011.log');print('initial stale-provider failure preserved')
 rows={}
 for x in j('prototype/records.json'):
  ph=x['phase'];n=x['module'];assert x['status']==0 and x['before']==x['after']==h(b('snapshots/'+ph+'/DiophantineConsistency/'+n+'.lean'));assert x['log_sha256']==h(b('prototype/'+ph+'-'+n+'.log')) and x['time']==b('prototype/'+ph+'-'+n+'.time').decode()
  for d in x['direct_inputs']:
   assert d['before']==d['after'];mod=d['module'].split('.')[-1]
   if mod==target: assert d['before']==rows[ph,target]['object_sha256'] and d['resolved']==rows[ph,target]['object']
   else:assert mod in providers and d['before']==providers[mod]['object_sha256'],(ph,n,mod)
  rows[ph,n]=x;print('build receipt',ph,n,x['time'].strip())
 for n in clients:assert rows['baseline',n]['object_sha256']==rows['final',n]['object_sha256'];print('client object hashes match',n)
 for x in j('prototype/coherent-probe-records.json'):
  ph=x['phase'];k=x['probe'];assert x['status']==0 and x['source_before']==x['source_after']==h(b('prototype/'+k+'.lean'));assert x['objects_before']==x['objects_after']==[rows[ph,target]['object_sha256']];assert x['log_sha256']==h(b('prototype/probe-'+ph+'-'+k+'.log'))
 for k in ['names','coherent-interfaces','simp','instances','private']:
  a=b('prototype/probe-baseline-'+k+'.log');assert a==b('prototype/probe-final-'+k+'.log');print('paired target probe equal',k,len(a.splitlines()))
 assert len([v for v in b('prototype/probe-baseline-names.log').splitlines() if v.startswith(b'DECL ')])==18
 for x in j('prototype/repeat-records.json'):
  ph=x['phase'];y=rows[ph,target];assert x['status']==0 and x['before']==x['after']==y['before'] and x['object_sha256']==y['object_sha256'];assert x['log_sha256']==h(b('prototype/repeat1-'+ph+'-'+target+'.log')) and x['time']==b('prototype/repeat1-'+ph+'-'+target+'.time').decode();assert [(d['module'],d['before']) for d in x['direct_inputs']]==[(d['module'],d['before']) for d in y['direct_inputs']];print('repeat',ph,x['time'].strip())
 reused=j('prototype/prior-reused-provider-manifest.json');rel=base+'SignedPellResidue.lean';old=reused['protected'][rel];oldobj=next(x['sha256'] for x in reused['reused_objects'] if x['source']==rel);sound=next(x for x in prior if x['module']=='ThirteenCarrierSoundness');assert next(d['before'] for d in sound['direct_inputs'] if d['module'].endswith('.SignedPellResidue'))==oldobj;current=h(subprocess.check_output(['git','show',m['source_commit']+':'+rel]));assert old!=current;print('cached SignedPell inventory old source',old,'object',oldobj,'commit source',current)
 expected={'LowMaskData','NativeSourceMask','NativeRadixDigits','Carrier66Source'};actual={d['module'].split('.')[-1] for x in providers.values() for d in x['direct_inputs']};assert expected<=actual;print('unmatched cached provider inputs acknowledged',sorted(expected))
 assert b'import DiophantineConsistency.CurrentCarrierArithmetic2011' in subprocess.check_output(['git','show',m['source_commit']+':Computability/DiophantineConsistency/Lean/DiophantineConsistency.lean']);assert any('umbrella' in x.lower() for x in m['limitations']);print('untested direct umbrella importer acknowledged')
 for ph in ['baseline','final']:
  for n in [target,*clients]:
   v=rows[ph,n];p=Path(v['object']);print('optional external object',ph,n,'MATCH' if p.is_file() and h(p.read_bytes())==v['object_sha256'] else 'MISSING OR CHANGED')
 assert not any(n.endswith('.olean') for n in names);print('no compiled objects archived; portable object hashes are receipt claims')
print('PASS')
