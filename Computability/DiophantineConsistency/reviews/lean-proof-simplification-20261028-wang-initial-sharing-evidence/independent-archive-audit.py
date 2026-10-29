from pathlib import Path
from zipfile import ZipFile
import hashlib,json,subprocess
P=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-wang-initial-sharing-evidence');D=json.loads((P/'BUNDLE.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest();J=lambda z,n:json.loads(z.read(n));root='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
def git(ref,path):return subprocess.check_output(['git','show',ref+':'+path])
def blocks(s):
 out={};key=None
 for line in s.decode().splitlines(keepends=True):
  if line.startswith('DECL '):key=line.split(' TYPE ',1)[0];assert key not in out;out[key]=''
  if key:out[key]+=line
 return out
assert sha((P/D['archive']).read_bytes())==D['archive_sha256'];assert subprocess.check_output(['git','rev-parse',D['source_commit']+'^'],text=True).strip()==D['source_parent'];review=(P/D['independent_review']['file']).read_bytes();assert sha(review)==D['independent_review']['sha256']
with ZipFile(P/D['archive']) as z:
 names=z.namelist();assert z.testzip() is None and len(names)==len(set(names)) and set(names)==set(D['members'])
 for name,v in D['members'].items():
  b=z.read(name);assert len(b)==v['bytes'] and sha(b)==v['sha256'],name
 assert z.read('independent/wang-initial-independent-review.txt')==review;print('ARCHIVE CRC/member hashes OK',len(names),D['archive_sha256'],'review',sha(review))
 rows=J(z,'prototype/records.json')+J(z,'prototype/client-records.json');assert len(rows)==12
 indexed={(x['phase'],x['module']):x for x in rows};assert len(indexed)==12
 providers=J(z,'provider/full-fresh-records.json');external=set()
 for x in rows:
  ph=x['phase'];mod=x['module'];ref=D['source_parent'] if ph=='baseline' else D['source_commit'];content=z.read(f'snapshots/{ph}/DiophantineConsistency/{mod}.lean');assert content==git(ref,root+mod+'.lean') and x['status']==0 and x['before']==x['after']==sha(content)
  assert sha(z.read('prototype/'+Path(x['log']).name))==x['log_sha256'];assert z.read('prototype/'+Path(x['command'][4]).name).decode()==x['time']
  for i in x['direct_inputs']:
   assert i['before']==i['after']; n=i['module'].split('.')[-1]
   if (ph,n) in indexed:assert i['before']==indexed[ph,n]['object_sha256']
   else:
    match=[p for p in providers if p['module']==i['module'] and p['status']==0 and p['object_sha256']==i['before']];assert match and any(p['source_sha256']==sha(git(D['source_commit'],root+n+'.lean')) for p in match);external.add(n)
  print('BUILD',ph,mod,x['time'].strip())
 assert external=={'ArithmeticWangTable','ArithmeticMachineRun215'};print('DIRECT PROVIDER source/receipt matches',sorted(external))
 for ph,ref in [('baseline',D['source_parent']),('final',D['source_commit'])]:
  for n in ['ArithmeticWangPlane','ArithmeticWangSoundness','ArithmeticRunTrace']:
   assert z.read(f'commit/{ph}/{n}.lean')==z.read(f'snapshots/{ph}/DiophantineConsistency/{n}.lean')==git(ref,root+n+'.lean')
 print('all 12 source snapshots and commit copies match')
 for recfile in ['prototype/probe-records.json','prototype/client-probe-records.json']:
  recs=J(z,recfile)
  for x in recs:
   assert x['status']==0 and x['source_before']==x['source_after']==sha(z.read('prototype/'+Path(x['source']).name)) and x['log_sha256']==sha(z.read('prototype/'+Path(x['log']).name))
   for ob in x['objects']:
    n=Path(ob['path']).stem;assert ob['before']==ob['after']==indexed[x['phase'],n]['object_sha256']
  print('PROBES',recfile,len(recs),'all source/log/recorded input hashes match')
 a=blocks(z.read('prototype/baseline-interfaces.log'));b=blocks(z.read('prototype/final-interfaces.log'));assert len(a)==148 and set(a)<=set(b) and all(a[k]==b[k] for k in a)
 added=sorted(set(b)-set(a));assert set(added)=={'DECL DiophantineConsistency.ArithmeticWangPlane.initial_action','DECL DiophantineConsistency.ArithmeticWangPlane.initial_action._proof_1','DECL DiophantineConsistency.ArithmeticWangPlane.initial_run_one'};print('COIMPORT',len(a),'common unchanged, added',added)
 for k in ['simp','instances','client-interfaces','client-simp','client-instances']:
  a=z.read(f'prototype/baseline-{k}.log');b=z.read(f'prototype/final-{k}.log');assert a==b;print('COMPARE',k,'identical lines',len(a.splitlines()))
 assert len(blocks(z.read('prototype/baseline-client-interfaces.log')))==73
 assert len(z.read('prototype/baseline-simp.log').splitlines())==29730 and len(z.read('prototype/baseline-instances.log').splitlines())==13383
 assert indexed['baseline','ArithmeticTilingTable']['object_sha256']!=indexed['final','ArithmeticTilingTable']['object_sha256'];print('CLIENT object hashes differ, named reports equal')
 search=J(z,'independent/wang-initial-independent-short-search.json');assert search['status']==1 and search['bytes']==0 and sha(z.read('independent/wang-initial-independent-short-search.log'))==search['log_sha256'];print('SHORT SEARCH',search['scope'])
 print('LIMITS',D['limitations'])
