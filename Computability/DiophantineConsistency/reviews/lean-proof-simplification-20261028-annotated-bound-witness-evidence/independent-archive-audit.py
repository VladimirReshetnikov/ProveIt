from pathlib import Path
import hashlib,json,zipfile,subprocess
D=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-annotated-bound-witness-evidence');M=json.loads((D/'BUNDLE.json').read_text());A=D/M['archive'];sha=lambda b:hashlib.sha256(b).hexdigest();assert sha(A.read_bytes())==M['archive_sha256'];assert subprocess.check_output(['git','rev-parse',M['source_commit']+'^'],text=True).strip()==M['source_parent']
with zipfile.ZipFile(A) as z:
 assert z.testzip() is None
 names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(M['members']);assert not any(n.endswith('.olean') for n in names)
 for n in names:
  b=z.read(n);v=M['members'][n];assert len(b)==v['bytes'] and sha(b)==v['sha256'],n
 print('ARCHIVE CRC, SHA-256 AND',len(names),'MEMBERS VERIFIED',M['archive_sha256'])
 def read(n):return z.read(n)
 def j(n):return json.loads(read(n))
 source='Computability/DiophantineConsistency/Lean/DiophantineConsistency/AnnotatedBound.lean'
 for phase,ref in [('baseline',M['source_parent']),('final',M['source_commit'])]:
  raw=subprocess.check_output(['git','show',ref+':'+source]);assert raw==read('commit/'+phase+'/AnnotatedBound.lean'); assert phase!='baseline' or raw==read('snapshots/baseline/DiophantineConsistency/AnnotatedBound.lean');print('GIT',phase,sha(raw))
 assert read('snapshots/variant3/DiophantineConsistency/AnnotatedBound.lean')==read('commit/final/AnnotatedBound.lean')
 review='independent/annotated-bound-independent-review.txt';assert read(review)==(D/'independent-review.txt').read_bytes();print('REVIEW',sha(read(review)))
 shared=j('prototype/directverify-records.json')+[x for x in j('prototype/common-prior-records.json') if x['module']=='NatIterate']+j('prototype/common2-records.json')
 for phase in ('base2','v3fresh'):
  recs=shared+j('prototype/'+phase+'-records.json');outputs={x['module']:x['object_sha256'] for x in recs}
  for x in recs:
   assert x['status']==0 and x['before']==x['after'];assert sha(read('prototype/'+Path(x['log']).name))==x['log_sha256'];timepath=x['command'][x['command'].index('-o')+1];assert read('prototype/'+Path(timepath).name).decode()==x['time']
   for d in x['direct_inputs']:
    assert d['before']==d['after'];n=d['module'].split('.')[-1]
    if n in outputs:assert d['before']==outputs[n],(phase,x['module'],n)
   mod=x['module'];prefix='snapshots/directverify/DiophantineConsistency/' if mod=='AnnotatedCodeArithmetic' else 'snapshots/common2/DiophantineConsistency/' if mod in {v['module'] for v in j('prototype/common2-records.json')} else 'snapshots/'+('baseline' if phase=='base2' else 'variant3')+'/DiophantineConsistency/'
   entry=prefix+mod+'.lean'
   if mod=='NatIterate':assert sha(subprocess.check_output(['git','show',M['source_parent']+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/NatIterate.lean']))==x['before']
   elif entry in names:assert sha(read(entry))==x['before'],(phase,mod,entry)
   else:raise AssertionError(('missing source',entry))
  print('BUILD RECEIPTS',phase,len(recs),'and locally built provider edges verified')
  for k in ('names','interfaces','simp','instances'):
   q=j('prototype/probe-'+k+'-'+phase+'.json');assert q['status']==0 and q['source_before']==q['source_after']==sha(read('prototype/'+Path(q['source']).name));assert q['object_before']==q['object_after']==outputs['AnnotatedBound'];assert q['log_sha256']==sha(read('prototype/'+Path(q['log']).name))
 for k,count in [('names',60),('simp',25317),('instances',11807)]:
  a=read('prototype/base2-'+k+'.log');b=read('prototype/v3fresh-'+k+'.log');assert a==b and len(a.splitlines())==count;print('PROBE',k,count)
 assert read('prototype/base2-interfaces.log')==read('prototype/v3fresh-interfaces.log');print('INTERFACES equal')
 for mod in ('AnnotatedBoundLocal','AnnotatedBoundScan'):
  a=next(x for x in j('prototype/base2-records.json') if x['module']==mod);b=next(x for x in j('prototype/v3fresh-records.json') if x['module']==mod);assert a['object_sha256']==b['object_sha256'];print('CLIENT RECEIPT',mod,a['object_sha256'])
 for phase in ('base2a','v3fresha','base2b','v3freshb'):
  x=j('prototype/'+phase+'-records.json')[0];assert x['status']==0 and read('prototype/'+Path(x['command'][x['command'].index('-o')+1]).name).decode()==x['time'] and sha(read('prototype/'+Path(x['log']).name))==x['log_sha256'];print('REPEAT',phase,x['time'].strip())
 for x in shared:
  mod=x['module'];path='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+mod+'.lean'
  assert sha(subprocess.check_output(['git','show',M['source_parent']+':'+path]))==x['before'],('provider commit mismatch',mod)
 for mod in ('AnnotatedBoundLocal','AnnotatedBoundScan'):
  raw=subprocess.check_output(['git','show',M['source_parent']+':Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+mod+'.lean'])
  assert raw==read('snapshots/baseline/DiophantineConsistency/'+mod+'.lean')==read('snapshots/variant3/DiophantineConsistency/'+mod+'.lean')
 print('PROVIDER AND CLIENT SOURCES match parent commit')
 for name,source_phase in [('repeatbaseline1','baseline'),('repeatfinal1','final'),('repeatbaseline2','baseline'),('repeatfinal2','final'),('variant2','variant2'),('repeatbaseline3','baseline'),('repeatvariant3a','variant3'),('repeatbaseline4','baseline'),('repeatvariant3b','variant3')]:
  x=j('prototype/'+name+'-records.json')[0];assert x['status']==0 and x['before']==x['after']==sha(read('snapshots/'+source_phase+'/DiophantineConsistency/AnnotatedBound.lean'))
  assert sha(read('prototype/'+Path(x['log']).name))==x['log_sha256'] and read('prototype/'+Path(x['command'][x['command'].index('-o')+1]).name).decode()==x['time']
  for d in x['direct_inputs']:assert d['before']==d['after']
  print('HISTORICAL',name,x['time'].strip())
 assert read('snapshots/final/DiophantineConsistency/AnnotatedBound.lean')!=read('commit/final/AnnotatedBound.lean')
 print('HISTORICAL snapshots/final is the superseded simp_all candidate, not the committed final')
 assert 'prototype/baseline-AnnotatedBoundLocal-interrupted.log' in names
 print('SCOPE: receipt object hashes checked for internal consistency; no .olean files in archive, so binary inputs are not independently reproduced. External/transitive providers remain cached.')
