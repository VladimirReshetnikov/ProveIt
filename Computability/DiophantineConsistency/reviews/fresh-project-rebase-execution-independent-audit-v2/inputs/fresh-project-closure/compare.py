#!/usr/bin/env python3
"""Compare two completed fresh-project runs; no Lean execution or provenance expansion."""
import hashlib,json,os,re,sys
from pathlib import Path
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def guard(g):
 for name,expected in g.items():
  p=Path(name)
  if expected is None:
   if os.path.lexists(p):raise ValueError(('unexpected path',name))
  elif not p.is_file() or str(p.resolve())!=expected['realpath'] or H(p)!=expected['sha256']:raise ValueError(('guard changed',name))
def compare(author,peer):
 paths=[Path(author),Path(peer)];states=[json.loads(x.read_text()) for x in paths];a,b=states
 if any(x['status']!='PASS' for x in states):raise ValueError('both builders must pass')
 for key in ('manifest_sha256','provider_receipt_sha256','foundation_input_sha256','lean_sha256','driver_sha256','expected_axiom_reports'):
  if a[key]!=b[key]:raise ValueError(('different fixed inputs',key))
 for state,path in zip(states,paths):
  manifest=Path(state['snapshot'])/'manifest.json';provider=Path(state['provider']);foundation_input=Path(state['foundation_input_path'])
  if H(manifest)!=state['manifest_sha256'] or H(provider)!=state['provider_receipt_sha256'] or H(foundation_input)!=state['foundation_input_sha256'] or H(state['lean_path'])!=state['lean_sha256']:raise ValueError('pinned input changed')
  m=json.loads(manifest.read_text());prov=json.loads(provider.read_text());fi=json.loads(foundation_input.read_text());names=m['order'];sources=m['sources'];records=state['records'];outputs=state['outputs'];lib=path.parent/'lib'
  foundation=Path(prov['root'])/'.lake/build/lib/lean/Foundation'
  if prov['status']!='BUILT' or prov['exit_code']!=0 or prov['manifest_sha256']!=H(foundation_input) or fi['lean_sha256']!=state['lean_sha256'] or Path(prov['overlay'])!=Path(state['package_overlay']) or (Path(prov['overlay'])/'Foundation').resolve()!=foundation.resolve():raise ValueError('provider identity')
  guard(prov['declared_external_guard'])
  for rel,digest in prov['foundation_artifacts'].items():
   q=foundation/rel
   if not q.is_file() or q.is_symlink() or H(q)!=digest:raise ValueError(('provider artifact',rel))
  if {str(q.relative_to(foundation)) for q in foundation.rglob('*') if q.is_file() or q.is_symlink()}!=set(prov['foundation_artifacts']):raise ValueError('provider inventory')
  if len(set(names))!=m['project_modules'] or len(names)!=len(sources) or [r['module'] for r in records]!=names or set(outputs)!=set(names):raise ValueError('project record or output coverage')
  if not names or names[-1]!=m['target']:raise ValueError('target coverage')
  seen=set();pkg=Path(state['package_overlay']);tool=Path(state['lean_path']).parent.parent/'lib/lean'
  for row in records:
   name=row['module'];source=Path(state['snapshot'])/sources[name]['snapshot_path'];obj=lib/(name.replace('.','/')+'.olean');g=outputs[name]
   if row['exit']!=0 or row['source_sha256']!=sources[name]['sha256'] or H(source)!=row['source_sha256']:raise ValueError(('source or exit',name))
   if str(obj) not in g or g[str(obj)] is None or g[str(obj)]['sha256']!=row['object_sha256'] or obj.is_symlink() or H(obj)!=row['object_sha256']:raise ValueError(('object binding',name))
   if H(row['log'])!=row['log_sha256']:raise ValueError(('log drift',name))
   text=Path(row['log']).read_text();reports=re.findall(r"^'[^']+' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
   if reports!=row['axiom_reports'] or (name==m['target'] and (len(reports)!=state['expected_axiom_reports'] or any({x.strip() for x in rep.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'} for rep in reports))):raise ValueError(('axiom reports',name))
   declared=set(sources[name]['imports']);actual=set(row['direct_inputs'])
   if not declared<=actual or actual-declared-{'Init'}:raise ValueError(('declared input coverage',name))
   for module,dep in row['direct_inputs'].items():
    q=Path(dep['path']);entry=state['guarded_companions'].get(str(q))
    if entry is None or entry['sha256']!=dep['sha256'] or H(q)!=dep['sha256']:raise ValueError(('direct input binding',name,module))
    if module in sources:
     if module not in seen or dep['kind']!='project' or q!=lib/(module.replace('.','/')+'.olean'):raise ValueError(('project input root or order',name,module))
    else:
     base={'package':pkg,'toolchain':tool}.get(dep['kind'])
     if base is None or q!=base/(module.replace('.','/')+'.olean'):raise ValueError(('external input root',name,module))
     if module.split('.')[0]=='Foundation' and (dep['kind']!='package' or not q.resolve().is_relative_to(foundation.resolve())):raise ValueError(('Foundation input root',name,module))
   seen.add(name)
  guard(state['guarded_companions'])
  for g in outputs.values():guard(g)
 for x,y in zip(a['records'],b['records']):
  for field in ('module','exit','source_sha256','log_sha256','object_sha256','axiom_reports'):
   if x[field]!=y[field]:raise ValueError(('row mismatch',x['module'],field))
  da={k:(v['kind'],v['sha256']) for k,v in x['direct_inputs'].items()};db={k:(v['kind'],v['sha256']) for k,v in y['direct_inputs'].items()}
  if da!=db:raise ValueError(('direct input mismatch',x['module']))
 return {'status':'MATCHED_PASS','rows':len(a['records']),'manifest_sha256':a['manifest_sha256'],'provider_receipt_sha256':a['provider_receipt_sha256'],'author_state_sha256':H(author),'peer_state_sha256':H(peer),'author_workspace_source_drift':a['workspace_source_drift'],'peer_workspace_source_drift':b['workspace_source_drift'],'scope':'Two separate project compilations using the same frozen sources, compiler, driver and Foundation provider. Package-transitive and dynamic ancestry remains inherited; this comparison does not replay Lean itself.'}
if __name__=='__main__':print(json.dumps(compare(sys.argv[1],sys.argv[2]),indent=2,sort_keys=True))
