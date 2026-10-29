from pathlib import Path
import hashlib,json,subprocess,zipfile
r=Path(__file__).resolve().parent;m=json.loads((r/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();assert h((r/m['archive']).read_bytes())==m['archive_sha256'];assert h((r/m['independent_review']['path']).read_bytes())==m['independent_review']['sha256']
with zipfile.ZipFile(r/m['archive']) as z:
 ns=z.namelist();assert len(ns)==len(set(ns)) and set(ns)==set(m['members']) and z.testzip() is None
 for n,meta in m['members'].items():
  b=z.read(n);assert len(b)==meta['bytes'] and h(b)==meta['sha256'] and not n.endswith(('.olean','.ilean','.o'))
 for ph,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  b=z.read('commit/'+ph+'/ArithmeticCellTransfer.lean');assert b==z.read('prototype/'+ph+'/DiophantineConsistency/ArithmeticCellTransfer.lean')==subprocess.check_output(['git','show',rev+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticCellTransfer.lean'])
  rows=json.loads(z.read('prototype/'+ph+'-records.json'));assert len(rows)==2
  for x in rows:
   assert x['status']==0 and x['before']==x['after']==h(z.read('prototype/'+ph+'/DiophantineConsistency/'+x['module']+'.lean'))
   assert h(z.read('prototype/'+ph+'-'+x['module']+'.log'))==x['log_sha256']; assert z.read('prototype/'+ph+'-'+x['module']+'.time').decode()==x['time']
  for x in json.loads(z.read('prototype/'+ph+'-probes.json')):
   assert x['status']==0 and x['source_before']==x['source_after']==h(z.read('prototype/'+Path(x['source']).name));assert x['objects_before']==x['objects_after']==[rows[0]['object_sha256']];assert h(z.read('prototype/'+Path(x['log']).name))==x['log_sha256']
 for x in json.loads(z.read('prototype/ArithmeticCellDecoding-probe-records.json')):
  rows=json.loads(z.read('prototype/'+x['phase']+'-records.json'));assert x['status']==0 and x['source_before']==x['source_after']==h(z.read('prototype/'+Path(x['source']).name));assert x['objects_before']==x['objects_after']==[y['object_sha256'] for y in rows];assert h(z.read('prototype/'+Path(x['log']).name))==x['log_sha256']
 for n in ['names','interfaces','simp','instances','ArithmeticCellDecoding-names','ArithmeticCellDecoding-interfaces','ArithmeticCellDecoding-simp','ArithmeticCellDecoding-instances']:
  assert z.read('prototype/baseline-'+n+'.log')==z.read('prototype/final-'+n+'.log')
 a=z.read('prototype/baseline-ArithmeticCellDecoding.log').decode().replace('/baseline/','/PHASE/');b=z.read('prototype/final-ArithmeticCellDecoding.log').decode().replace('/final/','/PHASE/');assert a==b and a.count('warning:')==1 and 'cell_digit' in a;assert z.read('prototype/baseline-ArithmeticCellTransfer.log')==z.read('prototype/final-ArithmeticCellTransfer.log')==b''
 providers={'ArithmeticStandardCasts':'binary-half-direct-final-supplement-records.json','ArithmeticModularCancellation':'shared-modular-cancel-records.json','ArithmeticCyclicWord':'cell-no-carry-refresh-records.json','ArithmeticCellLabels':'cell-no-carry-refresh-records.json','ArithmeticBinaryCarry':'binary-half-direct-final-records.json','ArithmeticBinaryPopulation':'binary-half-direct-final-records.json','ArithmeticWindowDigits':'cell-no-carry-refresh-records.json'}
 first=json.loads(z.read('prototype/final-records.json'))[0]; deps=first['direct_inputs']+first['extra_inputs']
 for name,p in providers.items():
  d=next(q for q in deps if q['module'].split('.')[-1]==name);sh=h(z.read('sources/'+name+'.lean'));xs=json.loads(z.read('providers/'+p));assert any(x['module'].split('.')[-1]==name and x['status']==0 and x['object_sha256']==d['before'] and x.get('source_before',x.get('before'))==x.get('source_after',x.get('after'))==sh for x in xs)
print('PASS',len(m['members']),'members, snapshots, paired records, probes, reports and seven provider associations')
