from pathlib import Path
import json,zipfile,hashlib,subprocess
p=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-cell-mod-cancel-evidence');j=json.loads((p/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();arc=p/j['archive'];assert h(arc.read_bytes())==j['archive_sha256'];review=(p/j['independent_review']['file']).read_bytes();assert h(review)==j['independent_review']['sha256']
with zipfile.ZipFile(arc) as z:
 assert z.testzip() is None and set(z.namelist())==set(j['members'])
 for n,v in j['members'].items():b=z.read(n);assert len(b)==v['bytes'] and h(b)==v['sha256']
 assert z.read('prototype/independent-review.txt')==review
 path='Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticCellTransfer.lean'
 for ph,ref in [('baseline',j['source_parent']),('final',j['source_commit'])]:assert z.read('source/'+ph+'.lean')==subprocess.check_output(['git','show',ref+':'+path])
 rs=json.loads(z.read('prototype/records.json'));assert len(rs)==4
 for x in rs:
  assert x['status']==0 and x['source_before']==x['source_after'];ph='baseline' if x['phase']=='base' else 'final'
  if x['module']=='ArithmeticCellTransfer':assert x['source_before']==h(z.read('source/'+ph+'.lean'))
  else:
   raw=subprocess.check_output(['git','show',j['source_commit']+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+x['module']+'.lean']);assert h(raw)==x['source_before']
  assert h(z.read('prototype/'+Path(x['command'][x['command'].index('-o')+1]).name))==h(x['time'].encode());assert h(z.read('prototype/'+x['phase']+'-'+x['module']+'.log'))==x['log_sha256']
  for d in x['inputs'].values():assert d['object_before']==d['object_after'] and d['source_before']==d['source_after']
  if x['module']=='ArithmeticCellDecoding':
   prev=next(q for q in rs if q['phase']==x['phase'] and q['module']=='ArithmeticCellTransfer');assert x['inputs']['DiophantineConsistency.ArithmeticCellTransfer']['object_before']==prev['object_sha256']
 clients=[x for x in rs if x['module']=='ArithmeticCellDecoding'];assert clients[0]['object_sha256']==clients[1]['object_sha256']
 prov=json.loads(z.read('provider/assembly-builds2.json'));refresh=json.loads(z.read('provider/support-refresh-records.json'));base=next(x for x in rs if x['phase']=='base' and x['module']=='ArithmeticCellTransfer')
 for n,d in base['inputs'].items():
  if n.endswith('ArithmeticCellLabels'):
   row=next(q for q in refresh if q['phase']=='fresh' and q['module']=='ArithmeticCellLabels');assert row['status']==0 and row['source_before']==row['source_after']==d['source_before'] and row['object_sha256']==d['object_before']
   local=next(q for q in refresh if q['phase']=='fresh' and q['module']=='ArithmeticCellLocal');assert local['status']==0 and row['inputs']['DiophantineConsistency.ArithmeticCellLocal']['object_before']==local['object_sha256']
  else:
   row=next(q for q in prov if q['module']==n);assert row['status']==0 and row['source_sha256']==d['source_before'] and row['object_sha256']==d['object_before']
 for x in json.loads(z.read('prototype/census-records.json')):
  assert x['status']==0 and x['before']==x['after']==h(z.read('prototype/'+Path(x['source']).name)) and x['direct_before']==x['direct_after']==next(t['object_sha256'] for t in rs if t['phase']==x['phase'] and t['module']=='ArithmeticCellTransfer') and x['log_sha256']==h(z.read('prototype/'+x['phase']+'-'+x['name']+'.log'))
 def text(n):return z.read('prototype/'+n).decode()
 def items(ph,k):return {s.split(k,1)[1].strip() for s in text(ph+'-names.log').splitlines() if k in s}
 a,b=items('base','DECL '),items('final','DECL ');sa,sb=items('base','SIMP '),items('final','SIMP ');assert len(a)==len(b)==60 and a==b and len(sa)==len(sb)==33296 and sa==sb
 assert text('base-interfaces.log')==text('final-interfaces.log') and sum(s.startswith('#check ') for s in text('interfaces.lean').splitlines())==60 and text('base-private.log')==text('final-private.log')==''
 assert 'five private reports' not in j['validation'] and any('instance census' in x for x in j['limitations']) and any('cached' in x for x in j['limitations'])
 print('CRC/archive hash,',len(j['members']),'BUNDLE member hashes/sizes, review hash, both commit/parent source snapshots verified')
 print('Four paired build receipts, eight direct-input before/after values, same-phase target links, six probe receipts, three project provider matches and claimed name/type/simp/empty-private outputs internally verified')
 print('scope: archived object hashes are not object binaries; cached transitive closure and unspecified clients remain unverified')
 print('archive SHA256',j['archive_sha256'],'review SHA256',j['independent_review']['sha256'])
