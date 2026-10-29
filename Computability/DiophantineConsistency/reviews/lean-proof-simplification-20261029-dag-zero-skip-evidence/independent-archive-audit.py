from pathlib import Path
import json,hashlib,zipfile,subprocess
D=next(Path('Computability/DiophantineConsistency/reviews').glob('*dag-zero-skip-evidence'));b=json.loads((D/'BUNDLE.json').read_text());Z=D/b['archive'];h=lambda d:hashlib.sha256(d).hexdigest();assert h(Z.read_bytes())==b['archive_sha256']
with zipfile.ZipFile(Z) as z:
 assert z.testzip() is None
 names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(b['members'])
 for n in names:
  x=z.read(n);assert h(x)==b['members'][n]['sha256'] and len(x)==b['members'][n]['bytes']
 print('ZIP SHA, CRC and member hashes/sizes verified',len(names));get=lambda n:z.read(n);rec=lambda n:json.loads(get('prototype/'+n));repo='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
 assert subprocess.check_output(['git','rev-parse',b['source_commit']+'^']).decode().strip()==b['source_parent'];n='ArithmeticRuntimeBoundDagRootA'
 for ph,ref in [('baseline',b['source_parent']),('final',b['source_commit'])]:
  data=subprocess.check_output(['git','show',ref+':'+repo+n+'.lean']);assert data==get(f'commit/{ph}.lean')==(get('prototype/baseline.lean') if ph=='baseline' else get(f'snapshots/src/DiophantineConsistency/{n}.lean'))
 assert get('independent/dag-zero-skip-independent-review.txt')==(D/'independent-review.txt').read_bytes();print('parent/commit target and independent review verified')
 prior=next(x for x in json.loads(get('provider/final-client-records.json')) if x['module']=='ArithmeticRuntimeBoundDagMacrosD' and x['phase']=='final' and x['status']==0);rows={}
 for x in rec('records.json'):
  ph=x['phase'];n=x['module'];src=get('commit/final.lean') if ph=='final' and n=='ArithmeticRuntimeBoundDagRootA' else subprocess.check_output(['git','show',b['source_parent']+':'+repo+n+'.lean']);assert x['status']==0 and x['source_before']==x['source_after']==h(src) and x['log_sha256']==h(get(f'prototype/{ph}-{n}.log')) and x['time'].encode()==get(f'prototype/{ph}-{n}.time')
  for name,d in x['inputs'].items():
   assert d['object_before']==d['object_after'] and d['source_before']==d['source_after'];m=name.split('.')[-1];assert d['source_before']==h(subprocess.check_output(['git','show',b['source_parent']+':'+repo+m+'.lean']))
   if m=='ArithmeticRuntimeBoundDagMacrosD':assert d['source_before']==prior['source_before']==prior['source_after'] and d['object_before']==prior['object_sha256']
   else:assert d['object_before']==rows[ph,m]['object_sha256']
  rows[ph,n]=x
 assert len(rows)==6
 for n in ['ArithmeticRuntimeBoundDagRootB','ArithmeticRuntimeBoundDagRootC']:assert rows['base',n]['object_sha256']==rows['final',n]['object_sha256']
 print('six builds and current-source MacrosD prior provider verified; clients match')
 for x in rec('census-records.json'):
  ph=x['phase'];n=x['name'];assert x['status']==0 and x['source_before']==x['source_after']==h(get(f'prototype/{n}.lean')) and x['log_sha256']==h(get(f'prototype/{ph}-{n}.log')) and x['time'].encode()==get(f'prototype/{ph}-{n}.time')
  for m,v in x['inputs_before'].items():assert v==x['inputs_after'][m]==rows[ph,m]['object_sha256']
 for n in ['interfaces','private']:assert get(f'prototype/base-{n}.log')==get(f'prototype/final-{n}.log')
 for k,num in [('DECL',324),('SIMP',29279),('INSTANCE',13370)]:
  read=lambda ph:{s for s in get(f'prototype/{ph}-names.log').decode().splitlines() if s.startswith(k+' ')}
  a,c=read('base'),read('final');assert a==c and len(a)==num;print(k,len(a))
 s=get('prototype/base-interfaces.log').decode();assert s.count('depends on axioms:')+s.count('does not depend on any axioms')==294;print('six census records and 294 public/generated type/axiom reports verified')
 print('compiled objects excluded; direct object links are recorded hashes; wider closure cached')
