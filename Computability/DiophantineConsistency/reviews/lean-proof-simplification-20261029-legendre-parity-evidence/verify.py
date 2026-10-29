from pathlib import Path
import hashlib,json,subprocess,zipfile
r=Path(__file__).resolve().parent;m=json.loads((r/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();assert h((r/m['archive']).read_bytes())==m['archive_sha256'];assert h((r/m['independent_review']['path']).read_bytes())==m['independent_review']['sha256']
with zipfile.ZipFile(r/m['archive']) as z:
 ns=z.namelist();assert len(ns)==len(set(ns)) and set(ns)==set(m['members']) and z.testzip() is None
 for n,meta in m['members'].items():
  b=z.read(n);assert len(b)==meta['bytes'] and h(b)==meta['sha256'] and not n.endswith(('.olean','.ilean','.o'))
 rec={}
 for ph in ['common','baseline','final']:
  rows=json.loads(z.read('prototype/'+ph+'-records.json'));assert [x['module'] for x in rows]==(['ArithmeticBinomFactorial'] if ph=='common' else ['ArithmeticBinomLegendre','ArithmeticHalfBinomial']);rec[ph]=rows
  for x in rows:
   assert x['status']==0 and x['before']==x['after']==h(z.read('prototype/'+ph+'/DiophantineConsistency/'+x['module']+'.lean'));assert h(z.read('prototype/'+ph+'-'+x['module']+'.log'))==x['log_sha256'];assert z.read('prototype/'+ph+'-'+x['module']+'.time').decode()==x['time']
   for d in x['direct_inputs']:
    n=d['module'].split('.')[-1];assert d['before']==d['after'] and d['source_before']==d['source_after']
    if n=='ArithmeticBinomLegendre':assert d['before']==rec[ph][0]['object_sha256'] and d['source_before']==rec[ph][0]['before']
    elif n=='ArithmeticBinomFactorial':assert d['before']==rec['common'][0]['object_sha256'] and d['source_before']==rec['common'][0]['before']
    else:assert d['source_before']==h(z.read('sources/'+n+'.lean'))
 for ph,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  b=z.read('commit/'+ph+'/ArithmeticBinomLegendre.lean');assert b==z.read('prototype/'+ph+'/DiophantineConsistency/ArithmeticBinomLegendre.lean')==subprocess.check_output(['git','show',rev+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticBinomLegendre.lean'])
  assert rec[ph][1]['before']==h(z.read('sources/ArithmeticHalfBinomial.lean'))
 assert rec['baseline'][1]['object_sha256']==rec['final'][1]['object_sha256']
 for probe in ['names','interfaces','simp','instances']:
  for ph in ['baseline','final']:
   x=json.loads(z.read(f'prototype/probe-{probe}-{ph}.json'));assert x['status']==0 and x['source_before']==x['source_after']==h(z.read('prototype/'+Path(x['source']).name));assert x['object_before']==x['object_after']==rec[ph][0]['object_sha256'];assert h(z.read('prototype/'+Path(x['log']).name))==x['log_sha256']
  assert z.read(f'prototype/baseline-{probe}.log')==z.read(f'prototype/final-{probe}.log')
 for probe,count in [('names',12),('interfaces',52),('simp',29039),('instances',13232)]:assert len(z.read(f'prototype/baseline-{probe}.log').splitlines())==count
 assert z.read('prototype/baseline-ArithmeticBinomLegendre.log').count(b'warning:')==3 and z.read('prototype/final-ArithmeticBinomLegendre.log').count(b'warning:')==1
 for name,p,rows,idx in [('ArithmeticBinaryPopulation','binary-half-direct-final-records.json',rec['baseline'][0],0),('ArithmeticBinomPascal','outer-seed-bound-sharing-prereq2-records.json',rec['common'][0],0)]:
  d=next(q for q in rows['direct_inputs'] if q['module'].split('.')[-1]==name);sh=h(z.read('sources/'+name+'.lean'));xs=json.loads(z.read('providers/'+p));assert any(x['module'].split('.')[-1]==name and x['status']==0 and x['object_sha256']==d['before'] and x.get('source_before',x.get('before',x.get('source_sha256')))==x.get('source_after',x.get('after',x.get('source_sha256')))==sh==d['source_before'] for x in xs)
print('PASS',len(m['members']),'members, source snapshots, paired records, 8 probes, warning counts and 2 prior provider associations')
