import hashlib,json,re,subprocess,zipfile
from pathlib import Path
r=Path(__file__).resolve().parent;m=json.loads((r/'BUNDLE.json').read_text());H=lambda x:hashlib.sha256(x).hexdigest();Z=zipfile.ZipFile(r/m['archive']);names=Z.namelist();assert Z.testzip() is None and len(names)==len(set(names)) and set(names)==set(m['members']) and H((r/m['archive']).read_bytes())==m['archive_sha256']
for n,x in m['members'].items():
 b=Z.read(n);assert len(b)==x['bytes'] and H(b)==x['sha256'] and not n.endswith(('.olean','.ilean','.o'))
assert H((r/m['independent_review']['file']).read_bytes())==m['independent_review']['sha256']==H(Z.read('independent/review.txt'))
D=lambda p:json.loads(Z.read('prototype/'+p));g=lambda p:H(Z.read(p)); w='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
for phase,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
 assert subprocess.check_output(['git','show',rev+':'+w+'ArithmeticWholeField.lean'])==Z.read(f'commit/{phase}/ArithmeticWholeField.lean')==Z.read(f'prototype/{phase}/DiophantineConsistency/ArithmeticWholeField.lean')
assert subprocess.check_output(['git','rev-parse',m['source_commit']+'^']).decode().strip()==m['source_parent']
records={}
for phase in ['baseline','final']:
 rows=D(phase+'-records.json');assert [x['module'] for x in rows]==['ArithmeticWholeField','ArithmeticOccupation'];records[phase]=rows
 for x in rows:
  assert x['status']==0 and x['before']==x['after']==g('prototype/'+phase+'/DiophantineConsistency/'+x['module']+'.lean') and x['log_sha256']==g('prototype/'+phase+'-'+x['module']+'.log') and x['time']==Z.read('prototype/'+phase+'-'+x['module']+'.time').decode()
  src=Z.read('prototype/'+phase+'/DiophantineConsistency/'+x['module']+'.lean').decode();assert re.findall(r'^import\s+(\S+)',src,re.M)==[d['module'] for d in x['direct_inputs']]
  for d in x['direct_inputs']:
   snap='prototype/'+phase+'/DiophantineConsistency/'+d['module'].split('.')[-1]+'.lean' if d['module'].endswith('.ArithmeticWholeField') else 'provider-sources/'+d['module'].split('.')[-1]+'.lean'
   assert d['before']==d['after'] and d['source_before']==d['source_after']==g(snap)
  assert all(d['before']==d['after'] for d in x['extra_inputs'])
 assert rows[1]['direct_inputs'][0]['before']==rows[0]['object_sha256']
 for p in D(phase+'-probes.json'):
  assert p['status']==0 and p['source_before']==p['source_after']==g('prototype/'+Path(p['source']).name) and p['objects_before']==p['objects_after']==[rows[0]['object_sha256']] and p['log_sha256']==g('prototype/'+phase+'-'+p['name']+'.log') and p['time_sha256']==g('prototype/'+phase+'-'+p['name']+'.time')
for x in D('ArithmeticOccupation-probe-records.json'):
 rows=records[x['phase']];di={d['module'].split('.')[-1]:d['before'] for row in rows for d in row['direct_inputs']};ex={d['module']:d['before'] for d in rows[1]['extra_inputs']};expected=[rows[0]['object_sha256'],rows[1]['object_sha256'],di['ArithmeticWangPlane'],ex['ArithmeticWangTable'],ex['ArithmeticMachineRun215'],di['ArithmeticCellDecoding'],ex['ArithmeticCellTransfer'],ex['ArithmeticCellLabels']]
 assert x['status']==0 and x['source_before']==x['source_after']==g('prototype/'+Path(x['source']).name) and x['objects_before']==x['objects_after']==expected and x['log_sha256']==g('prototype/'+x['phase']+'-ArithmeticOccupation-'+x['probe']+'.log')
for stem in ['simp','instances']:
 assert Z.read('prototype/baseline-'+stem+'.log')==Z.read('prototype/final-'+stem+'.log')
for stem in ['names','interfaces','simp','instances']:
 assert Z.read('prototype/baseline-ArithmeticOccupation-'+stem+'.log')==Z.read('prototype/final-ArithmeticOccupation-'+stem+'.log')
assert len(Z.read('prototype/baseline-ArithmeticOccupation-names.log').splitlines())==71
def decl(p):
 s=Z.read('prototype/'+p+'-interfaces.log').decode();return {x.group(1):x.group(0) for x in re.finditer(r'(?ms)^DECL (\S+) TYPE .*?(?=^DECL |\Z)',s)}
a,b=decl('baseline'),decl('final');assert len(a)==74 and len(b)==75 and not a.keys()-b.keys() and len(b.keys()-a.keys())==1 and next(iter(b.keys()-a.keys())).endswith('.orbit_isCell') and all(a[n]==b[n] for n in a)
provider=D('provider-record.json');assert provider['status']==0 and provider['before']==provider['after']==g('provider-sources/ArithmeticCellDecoding.lean') and provider['log_sha256']==g('prototype/provider.log') and provider['time']==Z.read('prototype/provider.time').decode()
prior=json.loads(Z.read('prior/dev/shm/cell-sum-unique/final-records.json')); plane=next(x for x in json.loads(Z.read('prior/dev/shm/wang-push-direct/final-target-records.json')) if x['module']=='ArithmeticWangPlane' and x['status']==0)
for phase in ['baseline','final']:
 rows=records[phase];d=next(d for d in rows[0]['direct_inputs'] if d['module'].endswith('.ArithmeticCellDecoding'));assert provider['object_sha256']==d['before'] and provider['before']==d['source_before'];ex={d['module']:d['before'] for d in rows[0]['extra_inputs']};px={x['module'].split('.')[-1]:x for x in provider['extra_inputs']+provider['direct_inputs']}
 for n in ['ArithmeticCellLabels','ArithmeticCellTransfer']:
  x=next(x for x in prior if x['module']==n and x['status']==0);assert x['before']==x['after']==g('provider-sources/'+n+'.lean') and x['object_sha256']==ex[n]==px[n]['before']==px[n]['after']
  for q in x['direct_inputs']:
   leaf=q['module'].split('.')[-1]
   if leaf=='ArithmeticCellLabels':assert q['before']==q['after']==ex[leaf]
   else: assert q['before']==q['after']==px[leaf]['before']==px[leaf]['after']
 d=next(d for d in rows[1]['direct_inputs'] if d['module'].endswith('.ArithmeticWangPlane'));assert plane['before']==plane['after']==d['source_before']==g('provider-sources/ArithmeticWangPlane.lean') and plane['object_sha256']==d['before']
 for n in ['ArithmeticWangTable','ArithmeticMachineRun215']:
  q=next(q for q in plane['direct_inputs'] if q['module'].endswith('.'+n));assert ex[n]==q['before']==q['after']
print('PASS',len(names),'members, hashes/CRC, snapshots, build receipts, exact probe pins, provider associations and declaration comparisons; compiled objects excluded')
