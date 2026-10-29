from pathlib import Path
import hashlib,json,subprocess,zipfile
r=Path(__file__).resolve().parent;m=json.loads((r/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();assert h((r/m['archive']).read_bytes())==m['archive_sha256'];assert h((r/m['independent_review']['path']).read_bytes())==m['independent_review']['sha256']
with zipfile.ZipFile(r/m['archive']) as z:
 ns=z.namelist();assert len(ns)==len(set(ns)) and set(ns)==set(m['members']) and z.testzip() is None
 for n,meta in m['members'].items():
  b=z.read(n);assert len(b)==meta['bytes'] and h(b)==meta['sha256'] and not n.endswith(('.olean','.ilean','.o'))
 for ph,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  for name in ['ArithmeticPellKnownUnit.lean','ArithmeticPellFirstNorm.lean']:
   x=z.read('commit/'+ph+'/'+name);assert x==z.read('prototype/'+ph+'/DiophantineConsistency/'+name)==subprocess.check_output(['git','show',rev+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+name])
  rows=json.loads(z.read('prototype/'+ph+'-records.json'));names=['ArithmeticPellKnownUnit','ArithmeticPellFirstNorm','ArithmeticPellKnownUnitChecks','ArithmeticPellCommonUnit','ArithmeticPellFirstNormChecks','ArithmeticPellFirstIndex'];assert [x['module'] for x in rows]==names
  for x in rows:
   assert x['status']==0 and x['before']==x['after']==h(z.read('prototype/'+ph+'/DiophantineConsistency/'+x['module']+'.lean'))
   assert x['log_sha256']==h(z.read('prototype/'+ph+'-'+x['module']+'.log')) and x['time']==z.read('prototype/'+ph+'-'+x['module']+'.time').decode()
   for d in x['direct_inputs']:
    name=d['module'].split('.')[-1];assert d['before']==d['after'] and d['source_before']==d['source_after']
    source=('prototype/'+ph+'/DiophantineConsistency/' if name in names else 'sources/')+name+'.lean';assert d['source_before']==h(z.read(source))
    if name in names:assert d['before']==next(y['object_sha256'] for y in rows if y['module']==name)
  probes=json.loads(z.read('prototype/'+ph+'-probes.json'));assert [x['name'] for x in probes]==['names','interfaces','simp','instances']
  for x in probes:
   assert x['status']==0 and x['source_before']==x['source_after']==h(z.read('prototype/'+Path(x['source']).name));assert x['objects_before']==x['objects_after']==[y['object_sha256'] for y in rows];assert x['log_sha256']==h(z.read('prototype/'+Path(x['log']).name)) and x['time_sha256']==h(z.read('prototype/'+Path(x['time']).name))
 a=json.loads(z.read('prototype/baseline-records.json'));b=json.loads(z.read('prototype/final-records.json'));assert [a[i]['object_sha256']==b[i]['object_sha256'] for i in range(2,6)]==[True,True,True,False]
 for n in ['simp','instances']:assert z.read('prototype/baseline-'+n+'.log')==z.read('prototype/final-'+n+'.log')
 def blocks(ph):return {s.split(' TYPE ',1)[0]:s.split(' TYPE ',1)[1] for s in z.read('prototype/'+ph+'-interfaces.log').decode().split('DECL ')[1:]}
 a,b=blocks('baseline'),blocks('final');old='_private.DiophantineConsistency.ArithmeticPellKnownUnit.0.DiophantineConsistency.ArithmeticPellKnownUnit.advance_iff';new='DiophantineConsistency.ArithmeticPellKnownUnit.advance_iff';assert a.keys()-b.keys()=={old} and b.keys()-a.keys()=={new} and len(a.keys()&b.keys())==38;assert all(a[k]==b[k] for k in a.keys()&b.keys()) and a[old].split()==b[new].split()
 producers={'ArithmeticPellClassification':'pell-positive-reflect-final-records.json','ArithmeticPellCongruences':'pell-y-add-final-records.json','ArithmeticGcdNormalization':'gcd-product-positivity-final-records.json','ArithmeticPellHalfIndex':'four-positive-wrappers-upstream-records.json'}
 for name,receipt in producers.items():
  rows=json.loads(z.read('providers/'+receipt));builds=json.loads(z.read('prototype/baseline-records.json'));d=next(d for x in builds for d in x['direct_inputs'] if d['module'].split('.')[-1]==name);assert any(x.get('module')==name and x.get('status')==0 and x.get('object_sha256')==d['before'] and x.get('before')==x.get('after')==d['source_before'] for x in rows)
print('PASS',len(m['members']),'members, snapshots, paired builds, six-object probes, reports and four direct provider associations')
