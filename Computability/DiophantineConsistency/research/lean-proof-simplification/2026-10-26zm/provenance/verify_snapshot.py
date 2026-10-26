#!/usr/bin/env python3
"""Offline Git-tree/blob/SHA256/coverage/delta replay. Does not invoke Lean."""
import hashlib,json,pathlib,sys
BASE=pathlib.Path(__file__).resolve().parents[1];P=BASE/'provenance';bad=[];counts={}
def read(name):return json.loads((P/name).read_text())
def gitsha(kind,data):return hashlib.sha1(kind.encode()+b' '+str(len(data)).encode()+b'\0'+data).hexdigest()
def check(test,what):
 if not test:bad.append(what)
def tree_hash(rows):
 rows=sorted(rows,key=lambda e:(e['path']+('/' if e['type']=='tree' else '')).encode())
 data=b''.join((e['mode'].lstrip('0')+' '+e['path']).encode()+b'\0'+bytes.fromhex(e['sha']) for e in rows)
 return gitsha('tree',data)
history={e['sha']:e for e in read('history.json')};pin=read('source_manifest.json')['commit'];oldpin=read('comparison_manifest.json')['commit']; trees={}
for name in ['root_tree.json','computability_tree.json','dc_root_tree.json','Lean_tree.json','H10_Lean_tree.json','BusyBeaver_tree.json','BusyBeaver_Lean_root_tree.json','BusyBeaver_modules_tree.json','BusyBeaver_ZFC_tree.json','HilbertTenthProblem_tree.json','BoundedZFC_tree.json','FirstOrder_tree.json','reviews_tree.json','previous_root_tree.json','previous_computability_tree.json','previous_target_root_tree.json','previous_Lean_tree.json','screen_DiophantineConsistency_tree.json','screen_checks_tree.json']:
 d=read(name);trees[name]=d;check(d.get('truncated') is False,[name,'missing complete-tree assertion'])
 dirs={'':[]}
 for e in d['tree']:
  parent,_,leaf=e['path'].rpartition('/');dirs.setdefault(parent,[]).append(dict(e,path=leaf))
 root_expected=history[pin if name=='root_tree.json' else oldpin]['commit']['tree']['sha'] if name in ['root_tree.json','previous_root_tree.json'] else d['sha']
 check(tree_hash(dirs[''])==root_expected,[name,'root-tree SHA mismatch'])
 entries={e['path']:e for e in d['tree']}
 for path,rows in dirs.items():
  if path:check(entries.get(path,{}).get('sha')==tree_hash(rows),[name,path,'nested tree SHA mismatch'])
def edge(parent,path,child):
 e=next((x for x in trees[parent]['tree'] if x['path']==path),{});check(e.get('sha')==trees[child]['sha'],[parent,path,child,'ancestor edge mismatch'])
for args in [('root_tree.json','Computability','computability_tree.json'),('computability_tree.json','DiophantineConsistency','dc_root_tree.json'),('dc_root_tree.json','Lean','Lean_tree.json'),('computability_tree.json','HilbertTenthProblem','HilbertTenthProblem_tree.json'),('HilbertTenthProblem_tree.json','Lean','H10_Lean_tree.json'),('computability_tree.json','BusyBeaver','BusyBeaver_tree.json'),('BusyBeaver_tree.json','Lean','BusyBeaver_Lean_root_tree.json'),('BusyBeaver_Lean_root_tree.json','BusyBeaver','BusyBeaver_modules_tree.json'),('BusyBeaver_modules_tree.json','ZFC','BusyBeaver_ZFC_tree.json'),('dc_root_tree.json','reviews','reviews_tree.json'),('previous_root_tree.json','Computability','previous_computability_tree.json'),('previous_computability_tree.json','DiophantineConsistency','previous_target_root_tree.json'),('previous_target_root_tree.json','Lean','previous_Lean_tree.json')]:edge(*args)
for root,name,child in [('BoundedZFC_root.json','BoundedZFCConsistency','BoundedZFC_tree.json'),('FirstOrder_root.json','FirstOrder','FirstOrder_tree.json')]:
 e=next(x for x in read(root) if x['name']==name);check(e['sha']==trees[child]['sha'],[root,'directory binding mismatch'])
for filename,root in [('source_manifest.json','sources'),('dependency_manifest.json','dependencies'),('comparison_manifest.json','comparison_sources')]:
 m=read(filename);counts[root]=len(m['sources'])
 for e in m['sources']:
  f=BASE/root/e['path']
  if not f.is_file():bad.append([root,e['path'],'missing']);continue
  d=f.read_bytes();check(gitsha('blob',d)==e['sha'],[root,e['path'],'blob SHA mismatch']);check(hashlib.sha256(d).hexdigest()==e['sha256'],[root,e['path'],'SHA256 mismatch'])
  if 'line_count' in e:check(len(d.splitlines())==e['line_count'],[root,e['path'],'line-count mismatch'])
def prefixed(name,prefix):return {prefix+e['path']:e['sha'] for e in read(name)['tree'] if e['type']=='blob'}
pre='Computability/DiophantineConsistency/Lean/';active=prefixed('Lean_tree.json',pre)
materialized={e['path']:e['sha'] for e in read('source_manifest.json')['sources'] if e['path'].startswith(pre)}
check(active==materialized,'active Lean coverage mismatch')
bindings={}
for name,prefix in [('root_tree.json',''),('dc_root_tree.json','Computability/DiophantineConsistency/'),('Lean_tree.json',pre),('H10_Lean_tree.json','Computability/HilbertTenthProblem/Lean/'),('BusyBeaver_modules_tree.json','Computability/BusyBeaver/Lean/BusyBeaver/'),('BusyBeaver_ZFC_tree.json','Computability/BusyBeaver/Lean/BusyBeaver/ZFC/'),('BoundedZFC_tree.json','SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/'),('FirstOrder_tree.json','Logic/FirstOrder/Lean/FirstOrder/')]:bindings.update(prefixed(name,prefix))
for name in ['source_manifest.json','dependency_manifest.json']:
 for e in read(name)['sources']:check(bindings.get(e['path'])==e['sha'],[name,e['path'],'fresh tree binding mismatch'])
def delta(oldtree,newtree,saved):
 old={e['path']:e['sha'] for e in read(oldtree)['tree'] if e['type']=='blob'};new={e['path']:e['sha'] for e in read(newtree)['tree'] if e['type']=='blob'}
 actual={k:(old.get(k),new.get(k)) for k in old.keys()|new.keys() if old.get(k)!=new.get(k)}
 expected={e['path']:(e['old_sha'],e['new_sha']) for e in read(saved)['files']};check(actual==expected,[saved,'delta mismatch']);return len(actual)
nd=delta('previous_Lean_tree.json','Lean_tree.json','active_tree_delta.json');ns=delta('screen_Lean_tree.json','Lean_tree.json','since_screen_delta.json')
screen=[]
for e in read('screen_Lean_root.json'):
 if e['type']=='file':screen.append({'path':e['name'],'sha':e['sha'],'type':'blob'})
 elif e['type']=='dir':
  child=read('screen_'+e['name']+'_tree.json');check(e['sha']==child['sha'],[e['name'],'screen subtree binding mismatch'])
  screen.extend(dict(x,path=e['name']+'/'+x['path']) for x in child['tree'])
check({e['path']:e['sha'] for e in screen}=={e['path']:e['sha'] for e in read('screen_Lean_tree.json')['tree']},'screen combined tree mismatch')
old_bindings=prefixed('previous_Lean_tree.json',pre)
for e in read('comparison_manifest.json')['sources']:check(old_bindings.get(e['path'])==e['sha'],[e['path'],'old tree binding mismatch'])
for e in read('active_tree_delta.json')['files']:
 for root,key in [('comparison_sources','old_lines'),('sources','new_lines')]:
  f=BASE/root/pre/e['path'];n=len(f.read_bytes().splitlines()) if f.exists() else 0;check(n==e[key],[e['path'],key,'delta line count mismatch'])
def ancestors(start):
 seen=set();todo=[start]
 while todo:
  x=todo.pop()
  if x in seen:continue
  seen.add(x)
  if x in history:todo.extend(e['sha'] for e in history[x]['parents'])
 return seen
for filename in ['commit_timeline.json','since_screen_commit_timeline.json']:
 timeline=read(filename);actual=ancestors(timeline['head'])-ancestors(timeline['base'])
 check(actual=={e['sha'] for e in timeline['commits']},[filename,'parent-graph commit membership mismatch'])
 check(len(actual)==timeline['commit_count'],[filename,'commit count mismatch'])
summary={'commit':pin,'commit_root_tree':history[pin]['commit']['tree']['sha'],'active_Lean_tree':trees['Lean_tree.json']['sha'],'checked':counts,'checked_tree_snapshots':len(trees),'active_Lean_files':len(active),'active_delta_files':nd,'since_closing_screen_delta_files':ns,'failures':bad,'Lean_elaboration':'not run','scope':'byte and tree identity only; not a proof check; dependencies are direct repository imports, not transitive closure'}
print(json.dumps(summary,indent=2));sys.exit(bool(bad))
