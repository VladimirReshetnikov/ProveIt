from pathlib import Path
import json,hashlib,zipfile,subprocess,re
p=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-dag-linear-bound-evidence');b=json.loads((p/'BUNDLE.json').read_text());arc=p/b['archive'];H=lambda v:hashlib.sha256(v).hexdigest();assert H(arc.read_bytes())==b['archive_sha256']
with zipfile.ZipFile(arc) as z:
 assert z.testzip() is None
 names=z.namelist(); assert len(names)==len(set(names)) and set(names)==set(b['members'])
 for n in names:
  d=z.read(n);meta=b['members'][n];assert len(d)==meta['bytes'] and H(d)==meta['sha256'];assert not n.endswith(('.olean','.ilean','.o','.c'))
 print('ZIP CRC, archive hash and',len(names),'manifest member hashes/sizes pass; no compiled objects')
 assert H((p/'independent-review.txt').read_bytes())==H(z.read('independent/dag-linear-independent-review.txt'));print('standalone independent review matches archived copy')
 commit=b['source_commit'];parent=b['source_parent'];assert subprocess.check_output(['git','rev-parse',commit+'^'],text=True).strip()==parent
 prefix='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
 for ph,ref in [('baseline',parent),('final',commit)]:
  for n in ('ArithmeticRuntimeBoundDagMacrosA','ArithmeticRuntimeBoundDagMacrosB'):
   data=subprocess.check_output(['git','show',ref+':'+prefix+n+'.lean']);assert data==z.read(f'commit/{ph}/{n}.lean')==z.read(f'snapshots/sources/{ph}/DiophantineConsistency/{n}.lean');print('git',ph,n,H(data))
  for n in ('ArithmeticRuntimeBoundDagMacrosC','ArithmeticRuntimeBoundDagMacrosD','ArithmeticRuntimeBoundDagRootA'):
   assert subprocess.check_output(['git','show',ref+':'+prefix+n+'.lean'])==z.read(f'snapshots/sources/{ph}/DiophantineConsistency/{n}.lean')
 print('all six client snapshots match corresponding commit/parent')
 rd=lambda name:json.loads(z.read(name));prior={}
 for f,n,phase,key in [('provider/dag-independent-audit/fol-refresh-records.json','BusyBeaver.ZFC.ArithmeticDagRootPerm222','shared','source_sha256'),('provider/dag-run-sharing/final-records.json','ArithmeticRuntimeBoundDagRun','final','before'),('provider/cantor-bound-simplify/build-records.json','ArithmeticEnumBoundTower','final','before')]:
  x=next(x for x in rd(f) if x.get('module',x.get('name'))==n and x.get('phase')==phase and x['status']==0);prior[n.split('.')[-1]]=(x[key],x['object_sha256']);print('prior receipt',n,*prior[n.split('.')[-1]])
 for n,path in [('ArithmeticDagRootPerm222','Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticDagRootPerm222.lean'),('ArithmeticRuntimeBoundDagRun',prefix+'ArithmeticRuntimeBoundDagRun.lean'),('ArithmeticEnumBoundTower',prefix+'ArithmeticEnumBoundTower.lean')]:
  assert H(subprocess.check_output(['git','show',commit+':'+path]))==prior[n][0];print('prior provider source matches source commit',n)
 rows={};direct=0
 for ph in ('baseline','final'):
  for fn in (f'prototype/{ph}-records.json',f'prototype/{ph}-client-records.json'):
   for x in rd(fn):
    n=x['module'];assert x['phase']==ph and x['status']==0 and x['source_before']==x['source_after']==H(z.read(f'snapshots/sources/{ph}/DiophantineConsistency/{n}.lean'))
    assert x['workspace_before']==x['workspace_after']==H(z.read(f'snapshots/sources/baseline/DiophantineConsistency/{n}.lean'))
    assert x['log_sha256']==H(z.read('prototype/'+Path(x['log']).name)) and x['time_sha256']==H(z.read('prototype/'+Path(x['time']).name));assert x['object_sha256']
    for d in x['direct_inputs']:
     m=d['module'].split('.')[-1];assert d['object_before']==d['object_after'] and d['source_before']==d['source_after']
     if m in prior:assert (d['source_before'],d['object_before'])==prior[m]
     else:
      y=rows[(ph,m)];assert d['resolved']==y['object'] and d['object_before']==y['object_sha256'] and d['source_before']==H(z.read(f'snapshots/sources/baseline/DiophantineConsistency/{m}.lean'))
     direct+=1
    rows[(ph,n)]=x
  for fn in (f'prototype/{ph}-probes.json',f'prototype/{ph}-short-probes.json'):
   for x in rd(fn):
    n=x['name'];obj='ArithmeticRuntimeBoundDagMacros'+n[0];assert x['status']==0 and x['source_before']==x['source_after']==H(z.read('prototype/'+Path(x['source']).name)) and x['object_before']==x['object_after']==rows[(ph,obj)]['object_sha256'] and x['log_sha256']==H(z.read('prototype/'+Path(x['log']).name)) and x['time_sha256']==H(z.read('prototype/'+Path(x['time']).name))
 print(len(rows),'successful builds,',direct,'direct-input records and 14 probe receipts agree with archived snapshots/logs/provider records')
 for n in ('ArithmeticRuntimeBoundDagMacrosC','ArithmeticRuntimeBoundDagMacrosD','ArithmeticRuntimeBoundDagRootA'):assert rows['baseline',n]['object_sha256']==rows['final',n]['object_sha256'];print('identical client objects',n)
 def parse(name):return {m.group(1):m.group(0) for m in re.finditer(r'^DECL (\S+) TYPE .*?(?=^DECL |\Z)',z.read(name).decode(),re.M|re.S)}
 moved="DiophantineConsistency.ArithmeticRuntimeBoundDagMacros.lin_le'"
 for level in ('A','B'):
  a=parse(f'prototype/baseline-{level}-interfaces.log');c=parse(f'prototype/final-{level}-interfaces.log');assert not a.keys()-c.keys() and all(a[n]==c[n] for n in a);assert c.keys()-a.keys()==({moved} if level=='A' else set());print(level,'namespace types/axioms baseline/final',len(a),len(c),'added',list(c.keys()-a.keys()))
  for n in ('simp','instances'):
   x=z.read(f'prototype/baseline-{level}-{n}.log');y=z.read(f'prototype/final-{level}-{n}.log');assert x==y;print(level,n,'match',len(x.splitlines()))
 assert z.read('prototype/baseline-A-short.log')==b'' and z.read('prototype/final-A-short.log').decode().strip()=='SHORT '+moved
 search=rd('prototype/declaration-search.json');assert search['status']==0 and len(search['stdout'].splitlines())==1 and 'ArithmeticRuntimeBoundDagMacrosB.lean:30:theorem lin_le\'' in search['stdout'];print('A-only short-name census and scoped repository declaration search pass')
 assert b'signal 2' in z.read('prototype/interrupted-baseline.time');print('incomplete interrupted setup disclosed')
 print('Scope: object bytes are excluded, and direct first-provider resolution cannot be independently recomputed from this archive alone; provider/source hashes and client outputs are receipt claims. Transitive closure remains cached; short-name search excludes other co-imports and non-simple declarations.')
