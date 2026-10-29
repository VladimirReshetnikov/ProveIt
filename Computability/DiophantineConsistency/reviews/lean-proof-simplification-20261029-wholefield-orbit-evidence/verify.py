from pathlib import Path
import hashlib,json,re,subprocess,zipfile
r=Path(__file__).resolve().parent;m=json.loads((r/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();assert h((r/m['archive']).read_bytes())==m['archive_sha256'];assert h((r/m['independent_review']['file']).read_bytes())==m['independent_review']['sha256']
with zipfile.ZipFile(r/m['archive']) as z:
 assert z.testzip() is None and len(z.namelist())==len(set(z.namelist())) and set(z.namelist())==set(m['members'])
 for n,d in m['members'].items():
  b=z.read(n);assert len(b)==d['bytes'] and h(b)==d['sha256'] and not n.endswith(('.olean','.ilean','.o'))
 for ph,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  p='Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticWholeField.lean';assert z.read('commit/'+ph+'/ArithmeticWholeField.lean')==subprocess.check_output(['git','show',rev+':'+p])==z.read('prototype/'+ph+'/DiophantineConsistency/ArithmeticWholeField.lean')
 for n in ['simp','instances']:
  assert z.read('prototype/baseline-'+n+'.log')==z.read('prototype/final-'+n+'.log')
 for n in ['names','interfaces','simp','instances']:
  assert z.read('prototype/baseline-ArithmeticOccupation-'+n+'.log')==z.read('prototype/final-ArithmeticOccupation-'+n+'.log')
 def decls(ph):
  a=re.split(r'(?m)(?=^DECL )',z.read('prototype/'+ph+'-interfaces.log').decode());return {t.split()[1]:t.strip() for t in a if t.startswith('DECL ')}
 a,b=decls('baseline'),decls('final');added=set(b)-set(a);assert len(a)==74 and len(b)==75 and not set(a)-set(b) and len(added)==1 and next(iter(added)).endswith('.orbit_isCell') and all(a[k]==b[k] for k in a)
 for ph in ['baseline','final']:
  rows=json.loads(z.read('prototype/'+ph+'-records.json'));assert [x['module'] for x in rows]==['ArithmeticWholeField','ArithmeticOccupation']
  for x in rows:
   assert x['status']==0 and x['before']==x['after'] and h(z.read('prototype/'+ph+'/DiophantineConsistency/'+x['module']+'.lean'))==x['before'] and h(z.read('prototype/'+ph+'-'+x['module']+'.log'))==x['log_sha256']
   for d in x['direct_inputs']:
    snapshot=('prototype/'+ph+'/DiophantineConsistency/' if d['module'].endswith('.ArithmeticWholeField') else 'provider-sources/')+Path(d['source']).name
    assert d['before']==d['after'] and d['source_before']==d['source_after'] and h(z.read(snapshot))==d['source_before']
  assert rows[1]['direct_inputs'][0]['before']==rows[0]['object_sha256']
  for x in json.loads(z.read('prototype/'+ph+'-probes.json')):
   assert x['status']==0 and x['objects_before']==x['objects_after']==[rows[0]['object_sha256']] and h(z.read('prototype/'+ph+'-'+x['name']+'.log'))==x['log_sha256']
 for x in json.loads(z.read('prototype/ArithmeticOccupation-probe-records.json')):
  assert x['status']==0 and x['objects_before']==x['objects_after'] and len(x['objects_before'])==8 and h(z.read('prototype/'+x['phase']+'-ArithmeticOccupation-'+x['probe']+'.log'))==x['log_sha256']
print('PASS 76 members, source snapshots, declaration comparisons and archived receipt consistency; compiled objects remain excluded')
