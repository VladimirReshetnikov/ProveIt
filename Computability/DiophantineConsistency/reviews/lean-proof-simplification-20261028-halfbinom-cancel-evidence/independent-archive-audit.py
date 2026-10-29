from pathlib import Path
import json,hashlib,subprocess,zipfile
P=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-halfbinom-cancel-evidence');D=json.loads((P/'BUNDLE.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest();J=lambda z,n:json.loads(z.read(n));path=lambda n:'Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+n+'.lean'
def git(ref,file):return subprocess.check_output(['git','show',ref+':'+file])
archive=(P/D['archive']).read_bytes();assert sha(archive)==D['archive_sha256'];assert subprocess.check_output(['git','rev-parse',D['source_commit']+'^'],text=True).strip()==D['source_parent']
rev=(P/D['independent_review']['file']).read_bytes();assert sha(rev)==D['independent_review']['sha256']
with zipfile.ZipFile(P/D['archive']) as z:
 names=z.namelist();assert z.testzip() is None and len(names)==len(set(names)) and set(names)==set(D['members'])
 for n,v in D['members'].items():
  b=z.read(n);assert len(b)==v['bytes'] and sha(b)==v['sha256'],n
 assert z.read('independent/halfbinom-independent-review.txt')==rev
 print('ARCHIVE',sha(archive),'members',len(names),'CRC OK; review',sha(rev))
 records={ph:J(z,f'prototype/{ph}-records.json') for ph in ['baseline','final']}
 for ph,ref in [('baseline',D['source_parent']),('final',D['source_commit'])]:
  for x in records[ph]:
   mod=x['module'];content=z.read(f'source/{ph}/{mod}.lean');assert content==git(ref,path(mod)) and sha(content)==x['before']==x['after'];print('SNAPSHOT',ph,mod,sha(content))
 providers=J(z,'provider/outer-seed-bound-sharing/prereq2-records.json')+J(z,'provider/pell-construction-refresh/resumed-records.json');matched=set()
 for ph in ['baseline','final']:
  rows=records[ph];built={x['module']:x for x in rows}
  for x in rows:
   assert x['status']==0 and x['workspace_before']==x['workspace_after'];assert sha(z.read('prototype/'+Path(x['log']).name))==x['log_sha256'];time=z.read('prototype/'+Path(x['time']).name);assert sha(time)==x['time_sha256'] and x['timing'].strip()==time.decode().strip()
   for d in x['direct_inputs']:
    assert d['before']==d['after'] and d['source_before']==d['source_after'];n=d['module'].split('.')[-1]
    if n in built:
     assert d['before']==built[n]['object_sha256'];assert d['source_before']==records['baseline'][0]['before'] if n=='ArithmeticHalfBinomial' else d['source_before']==built[n]['before']
    else:
     assert sha(git(D['source_commit'],path(n)))==d['source_before'];opts=[p for p in providers if p.get('module','').split('.')[-1]==n and p.get('status')==0 and p.get('object_sha256')==d['before'] and (p.get('before') or p.get('source_sha256'))==d['source_before']];assert opts,n;matched.add(n)
   print('BUILD',ph,x['module'],'OK',x['timing'])
 for n in ['ArithmeticHalfBinomial2011','ArithmeticOuterSeed']:
  a=next(x for x in records['baseline'] if x['module']==n);b=next(x for x in records['final'] if x['module']==n);assert a['object_sha256']==b['object_sha256'];print('CLIENT',n,'object hash identical',a['object_sha256'])
 assert matched=={'ArithmeticHalfBinomialSandwich','ArithmeticBinomExpansion','ArithmeticBinomLegendre','ArithmeticCarrierRadix2011'};print('PROVIDERS',sorted(matched),'source hashes and prior receipt object hashes agree')
 for k in ['names','interfaces','private','global-simp']:
  for ph in ['baseline','final']:
   x=J(z,f'prototype/{ph}-{k}-record.json');assert x['status']==0;assert x['source_before']==x['source_after']==sha(z.read(f'prototype/{k}.lean'));assert x['object_before']==x['object_after']==records[ph][0]['object_sha256'];assert x['log_sha256']==sha(z.read(f'prototype/{ph}-{k}.log'))
  a=z.read(f'prototype/baseline-{k}.log');b=z.read(f'prototype/final-{k}.log');assert a==b;print('PROBE',k,'equal lines',len(a.splitlines()))
 assert len(z.read('prototype/baseline-names.log').splitlines())==7 and len(z.read('prototype/baseline-global-simp.log').splitlines())==29056
 fail=J(z,'prototype/initial-failed-records.json')[0];assert fail['status']!=0 and fail['before']==fail['after']==sha(z.read('source/final/ArithmeticHalfBinomial.lean'));assert fail['log_sha256']==sha(z.read('prototype/initial-failed.log')) and fail['time_sha256']==sha(z.read('prototype/initial-failed.time'));assert b"unknown module prefix 'Foundation'" in z.read('prototype/initial-failed.log');print('INITIAL missing Foundation failure preserved')
 print('LIMITS',D['limitations'])
