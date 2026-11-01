#!/usr/bin/env python3
"""Authenticate matched intentionally interrupted 86/87 build prefixes before merge."""
from pathlib import Path
import collections,hashlib,json,os,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[3];C=R/'Computability/DiophantineConsistency';Q=C/'reviews/ipra-adaptive-native-current-rebase';M=Q/'manifest.json';DR=Q/'replay.py';A=Path('/tmp/ipra-adaptive-native-current-ur9xztxo');B=Path('/tmp/ipra-adaptive-native-current-qpk97_3z');P=Path('/tmp/ipra-bounded-induction-postmerge-wgkld2w0');PKG=Path('/tmp/pra14-full-transitive-2x6o__to/package-lib');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
h=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest(); m=json.loads(M.read_text());mh=h(M);dh=h(DR);ah=h(__file__);a=json.loads((A/'state.json').read_text());b=json.loads((B/'state.json').read_text());asum=h(A/'state.json');bsum=h(B/'state.json')
assert a['status']==b['status']=='FAILED' and a['failure']==b['failure']=='KeyboardInterrupt()'
assert a['manifest_sha256']==b['manifest_sha256']==mh and a['driver_sha256']==b['driver_sha256']==dh==m['driver_sha256']
assert h(P/'state.json')==m['parent_state_sha256'] and h(LEAN)==m['lean_sha256']
ra=a['records'];rb=b['records'];k=min(len(ra),len(rb));assert k>0
assert [r['name'] for r in ra[:k]]==[r['name'] for r in rb[:k]]==m['order'][:k]
prefix=set(m['order'][:k]);scheduled=set(m['order']); seen=set();rev=collections.defaultdict(set)
for n,p in m['source_files'].items():
 for x in re.findall(r'^import\s+([A-Z][\w.]*)',(R/p).read_text(),re.M):
  if x in m['source_files']:rev[x].add(n)
changed='DiophantineConsistency.IPRABoundedInduction';affected={changed};todo=[changed]
while todo:
 for x in rev[todo.pop()]:
  if x not in affected:affected.add(x);todo.append(x)
assert not (prefix & affected),sorted(prefix & affected)

def norm(path,root):
 try:return '$BUILD/'+str(Path(path).relative_to(root))
 except ValueError:return str(path)
for x,y in zip(ra[:k],rb[:k]):
 assert all(x[t]==y[t] for t in ['name','exit','object_sha256','log_sha256']) and x['exit']==0
 assert set(x['direct_imports'])==set(y['direct_imports'])
 for n in x['direct_imports']:
  p=x['direct_imports'][n];q=y['direct_imports'][n];assert p['sha256']==q['sha256'] and norm(p['resolved_path'],A)==norm(q['resolved_path'],B)
  assert n not in scheduled or n in seen,(x['name'],n)
 seen.add(x['name'])

def inventory():return {str((Path(d)/f).relative_to(P/'lib')) for d,_,fs in os.walk(P/'lib',followlinks=True) for f in fs if f.endswith('.olean')}
def audit():
 assert h(M)==mh and h(DR)==dh and h(__file__)==ah and h(A/'state.json')==asum and h(B/'state.json')==bsum
 assert h(P/'state.json')==m['parent_state_sha256'] and h(LEAN)==m['lean_sha256']
 assert all(h(R/p)==m['source_sha256'][n] for n,p in m['source_files'].items())
 assert all(h(Q/'sources'/(n.replace('.','/')+'.lean'))==m['source_sha256'][n] for n in m['order'])
 assert inventory()==set(m['parent_objects']) and all(h(P/'lib'/f)==v for f,v in m['parent_objects'].items())
 assert all(h(PKG/f)==v['sha256'] and str((PKG/f).resolve())==v['resolved_path'] for f,v in m['external_direct'].items())
 for row in ra[:k]:
  n=row['name'];rel=n.replace('.','/')+'.olean';log=n.replace('.','_')+'.log'
  for root in [A,B]:
   assert h(root/'lib'/rel)==row['object_sha256'] and h(root/'logs'/log)==row['log_sha256']
   for z in (ra if root==A else rb)[:k]:
    if z['name']==n:
     for dep in z['direct_imports'].values():assert h(dep['resolved_path'])==dep['sha256']
   assert not any(x in (root/'logs'/log).read_text() for x in ['warning:','error:','sorryAx'])
audit();D.mkdir(parents=True,exist_ok=True)
for label,root in [('author',A),('independent',B)]:
 shutil.copyfile(root/'state.json',D/(label+'-interrupted-state.json'));dest=D/(label+'-logs');dest.mkdir(exist_ok=True)
 for row in ra[:k]:
  f=row['name'].replace('.','_')+'.log';shutil.copyfile(root/'logs'/f,dest/f)
old=R/m['source_files'][changed];shutil.copyfile(old,D/'IPRABoundedInduction-before-merge.lean')
audit()
receipt={'status':'PASS','purpose':'Match and authenticate intentionally interrupted common prefix before source merge; this is not a completed endpoint build.','author_root':str(A),'peer_root':str(B),'author_state_sha256':asum,'peer_state_sha256':bsum,'manifest_sha256':mh,'driver_sha256':dh,'audit_sha256':ah,'common_count':k,'prefix':m['order'][:k],'rows':ra[:k],'changed_source':changed,'changed_reverse_cone':sorted(affected),'source_count':len(m['source_files']),'parent_object_count':len(m['parent_objects']),'external_file_count':len(m['external_direct']),'boundary':'Parent 848-module ancestor is author-only; package-transitive and dynamically loaded ancestry remain inherited, not exhaustively traced.'}
(D/'receipt.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n');print('PREFIX_AUDIT_PASS',k,'affected',sorted(affected),flush=True)
