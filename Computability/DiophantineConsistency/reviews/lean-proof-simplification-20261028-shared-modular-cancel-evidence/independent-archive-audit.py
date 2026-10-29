from pathlib import Path
import json,hashlib,zipfile,subprocess
D=next(Path('Computability/DiophantineConsistency/reviews').glob('*shared-modular-cancel-evidence'));b=json.loads((D/'BUNDLE.json').read_text());Z=D/b['archive'];h=lambda v:hashlib.sha256(v).hexdigest();assert h(Z.read_bytes())==b['archive_sha256']
with zipfile.ZipFile(Z) as z:
 assert z.testzip() is None
 names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(b['members'])
 for n in names:
  d=z.read(n);m=b['members'][n];assert h(d)==m['sha256'] and len(d)==m['bytes']
 print('archive SHA, CRC, member hashes and sizes verified',len(names))
 get=lambda n:z.read(n);rec=lambda n:json.loads(get('prototype/'+n));repo='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
 targets=['ArithmeticControllerLift','ArithmeticCellTransfer','ArithmeticPellResidueClasses'];clients=['ArithmeticControllerData','ArithmeticCellDecoding','ArithmeticPellHalfIndex'];helper='ArithmeticModularCancellation';assert subprocess.check_output(['git','rev-parse',b['source_commit']+'^']).decode().strip()==b['source_parent']
 for n in targets:
  for ph,ref in [('baseline',b['source_parent']),('final',b['source_commit'])]:
   data=subprocess.check_output(['git','show',ref+':'+repo+n+'.lean']);assert data==get(f'commit/{ph}/{n}.lean')==get(f'prototype/{ph}-commit-{n}.lean')
   if ph=='final':assert data==get(f'candidate/{n}.lean')
 for n in clients:assert get(f'commit/client/{n}.lean')==subprocess.check_output(['git','show',b['source_commit']+':'+repo+n+'.lean'])
 assert get(f'commit/final/{helper}.lean')==get(f'candidate/{helper}.lean')==subprocess.check_output(['git','show',b['source_commit']+':'+repo+helper+'.lean'])
 assert get('independent/shared-modular-independent-review.txt')==(D/'independent-review.txt').read_bytes();print('parent, commit, all sources and independent review verified')
 stats=subprocess.check_output(['git','show','--numstat','--format=',b['source_commit']]).decode();entries=[x.split('\t') for x in stats.splitlines()];assert sum(int(x[0]) for x in entries)==sum(int(x[1]) for x in entries)==33;print('33 insertions/33 deletions verified')
 prior=[]
 for f in ['provider/outer-seed-bound-sharing/prereq2-records.json','provider/outer-seed-bound-sharing/assembly-reused.json','provider/outer-seed-bound-sharing/assembly-builds2.json','provider/origin-block-sharing/records.json','provider/support-cast/refresh-records.json','provider/pell-balance-sharing/final-records.json']:
  for x in json.loads(get(f)):
   if x.get('status',0)==0:prior.append((x.get('module','').split('.')[-1],x.get('source_sha256',x.get('source_before',x.get('before'))),x.get('object_sha256')))
 rows={};seen=set()
 for x in rec('records.json'):
  ph=x['phase'];n=x['module'];assert x['status']==0 and x['source_before']==x['source_after'];source=get('candidate/'+n+'.lean') if ph=='probe' or (ph=='final' and n in targets) else get('commit/baseline/'+n+'.lean') if ph=='base' and n in targets else get('commit/client/'+n+'.lean');assert h(source)==x['source_before'];assert x['log_sha256']==h(get(f'prototype/{ph}-{n}.log')) and x['time'].encode()==get(f'prototype/{ph}-{n}.time')
  for k,d in x['inputs'].items():
   assert d['object_before']==d['object_after'] and d['source_before']==d['source_after'];m=k.split('.')[-1]
   if not d['source']:continue
   if m==helper:assert d['source_before']==rows['probe',m]['source_before'] and d['object_before']==rows['probe',m]['object_sha256']
   elif (ph,m) in rows:
    assert d['object_before']==rows[ph,m]['object_sha256']
    if m in targets:assert d['source_before']==h(get('commit/baseline/'+m+'.lean'))
   else:assert (m,d['source_before'],d['object_before']) in prior;seen.add(m);assert d['source_before']==h(subprocess.check_output(['git','show',b['source_commit']+':'+d['source']]))
  rows[ph,n]=x
 assert len(rows)==13 and len(seen)==7;print('13 build records and seven prior direct project provider pairs verified')
 assert subprocess.run(['git','cat-file','-e',b['source_parent']+':'+repo+helper+'.lean'],stderr=subprocess.DEVNULL).returncode!=0
 for n in targets:
  old=get('commit/baseline/'+n+'.lean').decode().splitlines();new=get('commit/final/'+n+'.lean').decode().splitlines();imp='import DiophantineConsistency.'+helper;assert imp not in old and imp in new
 print('new helper and three project imports verified')
 for n in clients:assert rows['base',n]['object_sha256']!=rows['final',n]['object_sha256']
 for x in rec('census-records.json'):
  ph=x['phase'];n=x['name'];assert x['status']==0 and x['before']==x['after']==h(get('prototype/'+n+'.lean')) and x['log_sha256']==h(get(f'prototype/{ph}-{n}.log')) and x['time'].encode()==get(f'prototype/{ph}-{n}.time')
  for m,v in x['inputs_before'].items():assert v==x['inputs_after'][m]==rows[ph,m]['object_sha256']
 for n in ['interfaces','private']:assert get(f'prototype/base-{n}.log')==get(f'prototype/final-{n}.log')
 for k,num in [('DECL',241),('SIMP',38882),('INSTANCE',16587)]:
  getset=lambda ph:{x for x in get(f'prototype/{ph}-names.log').decode().splitlines() if x.startswith(k+' ')}
  a,c=getset('base'),getset('final');assert a==c and len(a)==num;print(k,len(a))
 s=get('prototype/base-interfaces.log').decode();assert s.count('depends on axioms:')+s.count('does not depend on any axioms')==231
 x=rec('helper-interface-record.json');assert x['status']==0 and x['source_before']==x['source_after']==h(get('prototype/helper-interface.lean')) and x['log_sha256']==h(get('prototype/helper-interface.log')) and x['time'].encode()==get('prototype/helper-interface.time')
 for m,v in x['inputs_before'].items():assert v==x['inputs_after'][m]==rows['probe' if m==helper else 'final',m]['object_sha256']
 t=get('prototype/helper-interface.log').decode();assert 'HELPER DiophantineConsistency.ArithmeticModularCancellation.add_cancel SIMP false INSTANCE false' in t and all(w in t for w in ['propext','Classical.choice','Quot.sound']);print('census and helper registration/axioms verified')
 print('objects excluded; recorded object links checked, cached transitive closure not rebuilt')
