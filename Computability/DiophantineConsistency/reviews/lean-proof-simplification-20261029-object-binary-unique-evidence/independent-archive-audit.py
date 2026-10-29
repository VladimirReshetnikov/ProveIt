from pathlib import Path
import json,hashlib,subprocess,zipfile,re
root=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261029-object-binary-unique-evidence');m=json.loads((root/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();archive=root/m['archive'];assert h(archive.read_bytes())==m['archive_sha256'];prefix='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None;names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(m['members'])
 for n,v in m['members'].items():
  b=z.read(n);assert h(b)==v['sha256'] and len(b)==v['bytes'],n
 print('ZIP CRC, SHA and all',len(names),'members verified')
 read=lambda n:z.read(n); data=lambda n:json.loads(read('prototype/'+n));git=lambda ref,n:subprocess.check_output(['git','show',f'{ref}:{prefix}{n}.lean'])
 assert subprocess.check_output(['git','rev-parse',m['source_commit']+'^']).decode().strip()==m['source_parent']
 for ph,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  for n in ('ObjectCodeBound','ObjectCodeSeal'):assert read(f'snapshots/{ph}/DiophantineConsistency/{n}.lean')==git(rev,n)
  assert read(f'commit/{ph}.lean')==git(rev,'ObjectCodeBound')
 review=(root/m['independent_review']['file']).read_bytes();assert h(review)==m['independent_review']['sha256'] and review==read('independent/object-binary-unique-independent-review.txt');print('Git parent/commit snapshots and standalone review verified')
 rows={}
 for ph in ('provider','baseline','final','baseline-repeat','final-repeat','baseline-repeat2','final-repeat2'):
  for x in data(ph+'-records.json'):
   n=x['module'];assert x['status']==0 and x['before']==x['after'] and x['log_sha256']==h(read(f'prototype/{ph}-{n}.log')) and x['time'].encode()==read(f'prototype/{ph}-{n}.time')
   if n=='ObjectCodeClosure':assert x['before']==h(git(m['source_commit'],n))
   else:assert x['before']==h(read(f"snapshots/{'baseline' if ph.startswith('baseline') else 'final'}/DiophantineConsistency/{n}.lean"))
   for d in x['direct_inputs']:
    assert d['before']==d['after']
    if d['module'].endswith('.ObjectCodeClosure'):assert d['before']==rows['provider','ObjectCodeClosure']['object_sha256'] and d['resolved']==rows['provider','ObjectCodeClosure']['object']
    if d['module'].endswith('.ObjectCodeBound'):assert d['before']==rows[ph,'ObjectCodeBound']['object_sha256'] and d['resolved']==rows[ph,'ObjectCodeBound']['object']
   rows[ph,n]=x
 assert rows['baseline','ObjectCodeSeal']['object_sha256']==rows['final','ObjectCodeSeal']['object_sha256'];print('provider, paired target/client and two repeats, direct pins, equal client objects verified')
 for ph in ('baseline','final'):
  for n in ('names','interfaces','simp','instances'):
   x=data(f'probe-{n}-{ph}.json');assert x['status']==0 and x['source_before']==x['source_after']==h(read(f'prototype/{n}.lean')) and x['object_before']==x['object_after']==rows[ph,'ObjectCodeBound']['object_sha256'] and x['log_sha256']==h(read(f'prototype/{ph}-{n}.log'))
 def decl(ph):return {v.split(' TYPE ',1)[0]:v for v in re.split(r'(?m)^DECL ',read(f'prototype/{ph}-interfaces.log').decode()) if v.strip()}
 a,b=decl('baseline'),decl('final');assert len(a)==88 and len(b)==89 and all(b[k]==v for k,v in a.items()) and len(b.keys()-a.keys())==1 and 'binary_unique' in next(iter(b.keys()-a.keys()))
 for n,c in [('simp',12375),('instances',5184)]:
  a=read('prototype/baseline-'+n+'.log');b=read('prototype/final-'+n+'.log');assert a==b and len(a.splitlines())==c
 print('eight probe receipts, 88 unchanged declaration reports, helper and registrations verified')
 x=json.loads(read('snapshots/failed-probe/probe-names-baseline.json'));assert x['status']!=0 and x['source_before']==x['source_after']==h(read('snapshots/failed-probe/names.lean')) and x['log_sha256']==h(read('snapshots/failed-probe/baseline-names.log'))
 x=data('preliminary-final-records.json')[0];assert x['status']==0 and x['before']==x['after']==h(git(m['source_commit'],'ObjectCodeBound')) and x['log_sha256']==h(read('prototype/preliminary-final.log')) and x['time'].encode()==read('prototype/preliminary-final.time');print('failed probe and preliminary log/time retained; preliminary object absent')
 print('provider direct inputs are cached without matching source provenance; wider closure cached; archive omits object binaries')
