from pathlib import Path
import hashlib,json,zipfile,subprocess
p=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-pell-balance-evidence');j=json.loads((p/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();arc=p/j['archive'];assert h(arc.read_bytes())==j['archive_sha256'];review=(p/j['independent_review']['file']).read_bytes();assert h(review)==j['independent_review']['sha256'];exceptions=[]
with zipfile.ZipFile(arc) as z:
 assert z.testzip() is None and set(z.namelist())==set(j['members'])
 for n,v in j['members'].items():
  b=z.read(n);assert len(b)==v['bytes'] and h(b)==v['sha256']
 assert z.read('independent/pell-balance-independent-review.txt')==review
 names=[n for n in z.namelist() if n.startswith('source/') and n.endswith('.lean')];assert len(names)==26
 for n in names:
  _,ph,f=n.split('/');ref=j['source_parent'] if ph=='baseline' else j['source_commit'];raw=subprocess.check_output(['git','show',ref+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+f])
  if z.read(n)!=raw:
   assert ph=='baseline' and f in ('ArithmeticPellPeriodicity.lean','ArithmeticPellResidueClasses.lean');earlier=subprocess.check_output(['git','show','3b3572a2d6^:Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+f]);assert z.read(n)==earlier;exceptions.append(n)
 assert len(exceptions)==2
 def data(n):return json.loads(z.read('prototype/'+n))
 outputs={}
 for ph in ('baseline','final'):
  rows=[]
  for cat,expected in [('targets',2),('clients',4),('combined',7)]:
   xs=data(f'{ph}-{cat}-records.json');assert len(xs)==expected;rows+=xs
  by={'DiophantineConsistency.'+x['module']:x for x in rows};assert len(by)==13
  for x in rows:
   assert x['phase']==ph and x['status']==0 and x['before']==x['after']==h(z.read(f"source/{ph}/{x['module']}.lean"))
   assert h(z.read('prototype/'+Path(x['log']).name))==x['log_sha256']
   for d in x['direct_inputs']:
    assert d['before']==d['after']
    if d['module'] in by:assert d['before']==by[d['module']]['object_sha256']
   outputs[(ph,x['module'])]=x['object_sha256']
  for cat in ('ArithmeticPellRecurrence','ArithmeticPellClassification'):
   assert 'DiophantineConsistency.'+cat in by
 for n in ('ArithmeticPellRecurrenceChecks','ArithmeticPellClassificationChecks'):assert outputs[('baseline',n)]==outputs[('final',n)]
 for n in ('ArithmeticPellCongruences','ArithmeticPellKnownUnit','ArithmeticPellHalfIndex'):assert outputs[('baseline',n)]!=outputs[('final',n)]
 for name in [n for n in z.namelist() if n.startswith('prototype/probe-') and n.endswith('.json')]:
  x=json.loads(z.read(name));assert x['status']==0 and x['source_before']==x['source_after']==h(z.read('prototype/'+Path(x['source']).name)) and x['log_sha256']==h(z.read('prototype/'+Path(x['log']).name))
  for k in ('object','second_object'):
   if x.get(k):
    n=Path(x[k]).stem;assert x[k+'_before']==x[k+'_after']==outputs[(x['phase'],n)]
  if 'client_objects' in x:
   assert x['client_objects_before']==x['client_objects_after']
   for path,digest in zip(x['client_objects'],x['client_objects_before']):assert digest==outputs[(x['phase'],Path(path).stem)]
 def text(n):return z.read('prototype/'+n).decode()
 a={s[5:] for s in text('baseline-names.log').splitlines() if s.startswith('DECL ')};b={s[5:] for s in text('final-names.log').splitlines() if s.startswith('DECL ')};assert len(a)==78 and len(b)==79 and not a-b and b-a=={'DiophantineConsistency.ArithmeticPellRecurrence.norm_advance_balance'}
 for stem,count in [('simp',28968),('instances',13167),('half-simp',28977),('half-instances',13170)]:
  x=text('baseline-'+stem+'.log');assert x==text('final-'+stem+'.log') and len(x.splitlines())==count
 for stem in ('client-interfaces','half-interfaces'):assert text('baseline-'+stem+'.log')==text('final-'+stem+'.log')
 assert sum(s.startswith('DECL ') for s in text('baseline-half-interfaces.log').splitlines())==38
 base=text('baseline-interfaces.log');final=text('final-interfaces.log');start=final.index('DECL DiophantineConsistency.ArithmeticPellRecurrence.norm_advance_balance ');end=final.index('\nDECL ',start)+1;assert final[:start]+final[end:]==base
 assert any('predate' in s and 'reflection' in s for s in j['limitations']);assert any('cached' in s for s in j['limitations']);assert any('object hashes differ' in s for s in j['limitations']);assert any('ad hoc' in s for s in j['limitations'])
 print('CRC, archive hash,',len(j['members']),'member hashes/sizes, standalone/in-archive review hash verified')
 print('26 source snapshots: 24 match balance commit/parent; 2 baseline reflection snapshots match reflection commit parent and differ from balance parent, as disclosed')
 print('26 target/client/combined build receipts, same-phase direct-object relationships, all probe receipts, name/type/axiom/simp/instance output claims verified internally')
 print('limitations: cached transitive closure and external clients remain outside this archive audit; mixed baseline/final lanes do not isolate only the balance change')
 print('archive SHA256',j['archive_sha256'],'review SHA256',j['independent_review']['sha256'])
