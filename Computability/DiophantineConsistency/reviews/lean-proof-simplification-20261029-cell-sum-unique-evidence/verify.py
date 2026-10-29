from pathlib import Path
import hashlib,json,subprocess,zipfile,re
r=Path(__file__).resolve().parent;m=json.loads((r/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();assert h((r/m['archive']).read_bytes())==m['archive_sha256'];assert h((r/m['independent_review']['path']).read_bytes())==m['independent_review']['sha256']
with zipfile.ZipFile(r/m['archive']) as z:
 ns=z.namelist();assert len(ns)==len(set(ns)) and set(ns)==set(m['members']) and z.testzip() is None
 for n,meta in m['members'].items():
  b=z.read(n);assert len(b)==meta['bytes'] and h(b)==meta['sha256'] and not n.endswith(('.olean','.ilean','.o'))
 rec={}
 for ph,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  b=z.read('commit/'+ph+'/ArithmeticCellLabels.lean');assert b==z.read('prototype/'+ph+'/DiophantineConsistency/ArithmeticCellLabels.lean')==subprocess.check_output(['git','show',rev+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticCellLabels.lean'])
  rows=json.loads(z.read('prototype/'+ph+'-records.json'));assert [x['module'] for x in rows]==['ArithmeticCellLabels','ArithmeticCellTransfer'];rec[ph]=rows
  for x in rows:
   assert x['status']==0 and x['before']==x['after']==h(z.read('prototype/'+ph+'/DiophantineConsistency/'+x['module']+'.lean'));assert h(z.read('prototype/'+ph+'-'+x['module']+'.log'))==x['log_sha256'] and not z.read('prototype/'+ph+'-'+x['module']+'.log');assert z.read('prototype/'+ph+'-'+x['module']+'.time').decode()==x['time']
  assert h(z.read('sources/ArithmeticCellTransfer.lean'))==rows[1]['before']
  d=next(d for d in rows[1]['direct_inputs'] if d['module'].endswith('.ArithmeticCellLabels'));assert d['before']==d['after']==rows[0]['object_sha256'] and d['source_before']==d['source_after']==rows[0]['before']
 assert rec['baseline'][1]['object_sha256']==rec['final'][1]['object_sha256']
 probes=json.loads(z.read('prototype/probe-records.json'));assert len(probes)==16
 for x in probes:
  rows=rec[x['phase']];objs=rows[:2 if x['client'] else 1];assert x['status']==0 and x['source_before']==x['source_after']==h(z.read('prototype/'+Path(x['source']).name));assert x['objects_before']==x['objects_after']==[y['object_sha256'] for y in objs];assert h(z.read('prototype/'+Path(x['log']).name))==x['log_sha256']
 for n in ['simp','instances','client-names','client-interfaces','client-simp','client-instances']:assert z.read('prototype/baseline-'+n+'.log')==z.read('prototype/final-'+n+'.log')
 def interfaces(ph):
  s=z.read('prototype/'+ph+'-interfaces.log').decode();return {q.group(1):q.group(0) for q in re.finditer(r'(?ms)^DECL (\S+) TYPE .*?(?=^DECL |\Z)',s)}
 a,b=interfaces('baseline'),interfaces('final');assert len(a)==82 and len(b)==76 and sorted(a.keys()-b.keys())==[f'DiophantineConsistency.ArithmeticCellLabels.sum_le_one_cases._proof_{i}' for i in range(1,7)] and not(b.keys()-a.keys()) and all(a[n]==b[n] for n in a.keys()&b.keys())
 providers={'ArithmeticCellLocal':'high-digits-module-sharing-final-records.json','MFDoubledClause2011':'construction-share-bound-refresh-records.json','ArithmeticStandardCasts':'binary-half-direct-final-supplement-records.json','ArithmeticModularCancellation':'shared-modular-cancel-records.json','ArithmeticCyclicWord':'cell-no-carry-refresh-records.json'}
 deps=rec['final'][0]['direct_inputs']+rec['final'][1]['direct_inputs']
 for name,p in providers.items():
  d=next(q for q in deps if q['module'].split('.')[-1]==name);sh=h(z.read('sources/'+name+'.lean'));xs=json.loads(z.read('providers/'+p));assert any(x['module'].split('.')[-1]==name and x['status']==0 and x['object_sha256']==d['before'] and x.get('source_before',x.get('before',x.get('source_sha256')))==x.get('source_after',x.get('after',x.get('source_sha256')))==sh==d['source_before']==d['source_after'] for x in xs)
print('PASS',len(m['members']),'members, snapshots, paired records, 16 probes, interfaces and five provider associations')
