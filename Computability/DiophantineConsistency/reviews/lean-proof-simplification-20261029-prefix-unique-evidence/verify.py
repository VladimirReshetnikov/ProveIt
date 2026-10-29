from pathlib import Path
import hashlib,json,subprocess,zipfile,re
r=Path(__file__).resolve().parent;m=json.loads((r/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();assert h((r/m['archive']).read_bytes())==m['archive_sha256'] and h((r/m['independent_review']['path']).read_bytes())==m['independent_review']['sha256']
with zipfile.ZipFile(r/m['archive']) as z:
 ns=z.namelist();assert len(ns)==len(set(ns)) and set(ns)==set(m['members']) and z.testzip() is None
 for n,meta in m['members'].items():
  b=z.read(n);assert len(b)==meta['bytes'] and h(b)==meta['sha256'] and not n.endswith(('.olean','.ilean','.o'))
 rec={}
 for ph,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  b=z.read('commit/'+ph+'/ArithmeticCellDecoding.lean');assert b==z.read('refresh/'+ph+'/DiophantineConsistency/ArithmeticCellDecoding.lean')==subprocess.check_output(['git','show',rev+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticCellDecoding.lean'])
  rows=json.loads(z.read('refresh/'+ph+'-records.json'));assert [x['module'] for x in rows]==['ArithmeticCellDecoding','ArithmeticWholeField'];rec[ph]=rows
  for x in rows:
   assert x['status']==0 and x['before']==x['after']==h(z.read('refresh/'+ph+'/DiophantineConsistency/'+x['module']+'.lean'));assert h(z.read('refresh/'+ph+'-'+x['module']+'.log'))==x['log_sha256'] and z.read('refresh/'+ph+'-'+x['module']+'.time').decode()==x['time']
  assert h(z.read('sources/ArithmeticWholeField.lean'))==rows[1]['before'];d=next(d for d in rows[1]['direct_inputs'] if d['module'].endswith('.ArithmeticCellDecoding'));assert d['before']==d['after']==rows[0]['object_sha256'] and d['source_before']==d['source_after']==rows[0]['before']
  probes=json.loads(z.read('refresh/'+ph+'-probes.json'));old=json.loads(z.read('original/'+ph+'-probes.json'));assert len(probes)==len(old)==8
  for x,y in zip(probes,old):
   assert x['status']==y['status']==0 and x['name']==y['name'] and x['source_before']==x['source_after']==y['source_before']==y['source_after']==h(z.read('refresh/'+Path(x['source']).name));assert x['objects_before']==x['objects_after']==[q['object_sha256'] for q in rows];assert h(z.read('refresh/'+Path(x['log']).name))==x['log_sha256']==y['log_sha256'] and h(z.read('refresh/'+Path(x['time']).name))==x['time_sha256']
 for mod in ('ArithmeticCellDecoding','ArithmeticWholeField'):
  for kind in ('simp','instances'):assert z.read('refresh/baseline-'+mod+'-'+kind+'.log')==z.read('refresh/final-'+mod+'-'+kind+'.log')
  def reports(ph):
   s=z.read('refresh/'+ph+'-'+mod+'-interfaces.log').decode();return {q.group(1):q.group(0) for q in re.finditer(r'(?ms)^DECL (\S+) TYPE .*?(?=^DECL |\Z)',s)}
  a,b=reports('baseline'),reports('final');rem=sorted(a.keys()-b.keys());add=sorted(b.keys()-a.keys());chg=sorted(k for k in a.keys()&b.keys() if a[k]!=b[k])
  if mod=='ArithmeticWholeField':assert len(a)==len(b)==75 and not rem and not add and not chg
  else:
   pre='DiophantineConsistency.ArithmeticCellDecoding.prefix_unique.';assert len(a.keys()&b.keys())==69 and rem==[pre+'_simp_1',pre+'_simp_2'] and add==[pre+'_proof_1'] and chg==[pre+'_proof_2']
  logs=[z.read('refresh/'+p+'-'+mod+'.log').decode() for p in ('baseline','final')];clean=lambda s:re.sub(r'/dev/shm/prefix-unique-refresh/(baseline|final)/DiophantineConsistency/[^:]+:\d+:\d+:','SOURCE:',s);assert clean(logs[0])==clean(logs[1]) and logs[0].count('warning:')==(1 if mod=='ArithmeticCellDecoding' else 11)
 x=json.loads(z.read('refresh/provider-transfer-record.json'));assert x['status']==0 and x['before']==x['after']==h(z.read('sources/ArithmeticCellTransfer.lean')) and x['log_sha256']==h(z.read('refresh/provider-transfer.log')) and x['time']==z.read('refresh/provider-transfer.time').decode()
 for ph in ('baseline','final'):
  d=rec[ph][0]['direct_inputs'][0];assert d['before']==d['after']==x['object_sha256'] and d['source_before']==d['source_after']==x['before']
 prior=json.loads(z.read('providers/cell-selector-unit-final-records.json'))
 for n in ('ArithmeticCellLocal','ArithmeticCellLabels'):
  d=next(d for d in x['extra_inputs'] if d['module']==n);q=next(q for q in prior if q['module']==n);assert q['status']==0 and q['before']==q['after']==h(z.read('sources/'+n+'.lean')) and q['object_sha256']==d['before']==d['after']
 for d in x['direct_inputs']:
  n=d['module'].split('.')[-1];assert d['source_before']==d['source_after']==h(z.read('sources/'+n+'.lean')) and d['before']==d['after']
print('PASS',len(m['members']),'members, git snapshots, paired builds, 16 refreshed probes, original log hashes, interface comparisons, warning counts and refreshed provider associations')
