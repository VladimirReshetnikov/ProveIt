from pathlib import Path
import hashlib,json,zipfile,subprocess
P=Path(__file__).resolve().parent; m=json.loads((P/'BUNDLE.json').read_text());zpath=P/m['archive'];h=lambda b:hashlib.sha256(b).hexdigest()
assert h(zpath.read_bytes())==m['archive_sha256']
with zipfile.ZipFile(zpath) as z:
 assert z.testzip() is None
 names=z.namelist(); assert len(names)==len(set(names))==len(m['members'])==369
 assert set(names)==set(m['members'])
 for n in names:
  b=z.read(n); assert len(b)==m['members'][n]['bytes'] and h(b)==m['members'][n]['sha256']
  assert not n.endswith(('.olean','.ilean','.o'))
 print('ZIP CRC and complete 369-member sizes/hashes pass; no compiled objects')
 rev=(P/m['independent_review']['file']).read_bytes()
 assert rev==z.read('independent/review.txt')==(P/'independent-review.txt').read_bytes()
 assert h(rev)==m['independent_review']['sha256']
 print('Corrected peer review matches standalone and manifest')
 prefix='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
 targets=['ArithmeticCellLocal','CurrentHighDigits2011','MFCurrentHighDigits2011']
 for n in targets:
  assert z.read('selected/baseline/DiophantineConsistency/'+n+'.lean')==subprocess.check_output(['git','show',m['source_parent']+':'+prefix+n+'.lean'])
 for n in targets+['CurrentHighDigitFacts2011']:
  assert z.read('selected/final/DiophantineConsistency/'+n+'.lean')==subprocess.check_output(['git','show',m['source_commit']+':'+prefix+n+'.lean'])
 assert subprocess.check_output(['git','rev-parse',m['source_commit']+'^']).decode().strip()==m['source_parent']
 assert subprocess.run(['git','cat-file','-e',m['source_parent']+':'+prefix+'CurrentHighDigitFacts2011.lean'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode!=0
 print('All three baseline/parent and four final/commit sources match; helper absent from parent')
 omitted=json.loads(z.read('bundle/omitted-logs.json')); assert len(omitted)==26 and len({x['path'] for x in omitted})==26
 for x in omitted:
  p=Path(x['path']); assert p.is_file() and p.stat().st_size==x['bytes'] and h(p.read_bytes())==x['sha256']
  assert x['path'] not in names
 print('All 26 omitted external log originals, sizes and SHA-256 hashes pass')
 comparison=json.loads(z.read('selected/interfaces-comparison.json'))
 assert (comparison['baseline_count'],comparison['final_count'],len(comparison['removed']),len(comparison['added']),len(comparison['changed_common']))==(409,322,144,57,14)
 assert 409-144==265 and 265-14==251
 assert all('._proof_' in x for x in comparison['changed_common'])
 for name in targets:
  v2=json.loads(z.read('selected/v2-env-'+name+'-records.json')); assert len(v2)==2 and all(r['status']==0 and r['objects_before']==r['objects_after'] for r in v2)
  for r in v2:
   assert any(x['path']==r['log'] and x['sha256']==r['log_sha256'] for x in omitted)
 print('Interface counts and selected census receipt-to-omitted-log pins match')
 producers=json.loads(z.read('selected/direct-producer-audit.json')); assert len(producers)==36
 matched=0
 for item in producers:
  options=[]
  for r in item['matches']:
   path=Path(r['receipt']); entry='prior/'+path.parent.name+'/'+path.name
   if entry not in names: continue
   records=json.loads(z.read(entry)); candidates=[]
   def walk(o):
    if isinstance(o,list):
     for v in o: walk(v)
    elif isinstance(o,dict):
     if str(o.get('module',o.get('name',''))).split('.')[-1]==item['module'] and o.get('status')==0 and o.get('object_sha256')==item['object'] and o.get('source_sha256_before',o.get('source_sha256',o.get('before')))==item['source']: candidates.append(o)
     for v in o.values():walk(v)
   walk(records)
   if candidates: options.append(entry)
  if options: matched+=1
  else: assert item['module']=='NativeCyclicCarry' and not item['matches']
 assert matched==35
 print('Archived prior receipts substantiate 35/36 external provider pair mappings')
 for entry in ['alternative-full/baseline-records.json','selected/final-records.json','selected/supplement-baseline-records.json','selected/supplement-final-records.json']:
  rows=json.loads(z.read(entry)); assert all(r['status']==0 for r in rows)
  for r in rows:
   n=entry.split('/')[0]+'/'+Path(r['log']).name
   assert n in names and h(z.read(n))==r['log_sha256'],(entry,n)
 print('All archived main and supplemental successful build records match archived logs')
 assert '251 matching common reports, including all named user-facing theorem reports' in m['validation']
 assert 'not saved' in z.read('independent/review.txt').decode()
 print('Corrected wording and unsaved setup-output disclosure present')
print('PASS')
