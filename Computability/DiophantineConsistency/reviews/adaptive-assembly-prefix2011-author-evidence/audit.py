from pathlib import Path
import hashlib,json,os,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=Path(os.environ['ADAPTIVE_ASSEMBLY_BASE']);D=Path('/tmp/adaptive13-cell-root-parent-wnvsel13');roots={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver','FirstOrder':R/'Logic/FirstOrder/Lean/FirstOrder','PAHF':R/'Logic/Interpretability/PAHF/Lean/PAHF'}
targets={'DiophantineConsistency.'+x for x in ['ArithmeticControllerChoice','ArithmeticController','MFWangTiles942PhysicalData','MFWangTiles942PhysicalOrder','ArithmeticConstructionKernel','ArithmeticConstructionUnit','ArithmeticConstructionVariation']};seen=set();rows=[];boundary=set();missing=[];bad=[]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
bs=read(B/'state.json');ds=read(D/'state.json');assert bs['status']=='PASS' and ds['status']=='FAILED' and len(ds['records'])==37 and ds['records'][-1]['exit']==137
prefix={(r['namespace']+'.'+r['name'].replace('/','.')):r for r in ds['records'][:-1]};assert len(prefix)==36
for m,r in prefix.items():
 ns,n=m.split('.',1);f=roots[ns]/(n.replace('.','/')+'.lean');o=D/'lib'/ns/(n.replace('.','/')+'.olean');assert sha(f)==r['source_sha256'] and sha(o)==r['object_sha256']
def visit(m):
 if m in seen:return
 seen.add(m);ns,_,n=m.partition('.')
 if ns not in roots:boundary.add(m);return
 src=roots[ns]/(n.replace('.','/')+'.lean')
 if not src.is_file():boundary.add(m);return
 imports=[item for line in src.read_text().splitlines() if line.startswith('import ') for item in line.split('--',1)[0][len('import '):].split()]
 for x in imports:visit(x)
 if m in targets:return
 rel=Path(ns)/(n.replace('.','/')+'.olean');baseobj=B/'lib'/rel;donor=D/'lib'/rel if m in prefix else None
 if donor and baseobj.is_file():assert sha(donor)==sha(baseobj),(m,'prefix overlap differs')
 obj=baseobj if baseobj.is_file() else donor
 if not obj or not obj.is_file():missing.append(m);return
 resolved=obj.resolve();r={'module':m,'source_sha256':sha(src),'object_sha256':sha(obj),'object':str(obj),'resolved_object':str(resolved),'imports':imports}
 if m in prefix:
  assert sha(src)==prefix[m]['source_sha256'] and sha(obj)==prefix[m]['object_sha256'];r['provenance']='authenticated 36-module prefix'
 else:
  home=next((x.parent for x in resolved.parents if x.name=='lib'),None);record=None
  if home and (home/'state.json').is_file():
   state=read(home/'state.json')
   for x in state.get('records',state.get('completed',[])):
    if x.get('module')==m or (x.get('name')==n.replace('.','/') and x.get('namespace',ns)==ns):record=x;break
  if record and record.get('source_sha256'):
   if record['source_sha256']!=sha(src):bad.append((m,'source differs'))
   if record.get('object_sha256') and record['object_sha256']!=sha(obj):bad.append((m,'object differs'))
   r['provenance']='provider state'
  elif '/tmp/object-current-deps-_hgxk1r0/' in str(resolved):
   x=next((x for x in read('/tmp/object-current-deps-_hgxk1r0/dependency-replay.json')['modules'] if x.get('module')==m),None)
   if not x or x['source_sha256']!=sha(src):bad.append((m,'dependency metadata mismatch'))
   r['provenance']='dependency replay metadata'
  elif str(resolved).startswith('/home/codex/.codex/worktrees/62ff/Proofs/.lake/'):
   other=Path('/home/codex/.codex/worktrees/62ff/Proofs')/src.relative_to(R)
   if not other.is_file() or sha(other)!=sha(src):bad.append((m,'62ff source mismatch'))
   r['provenance']='62ff cache boundary; source matches, no cache-to-source proof'
  else:r['provenance']='unmatched boundary';bad.append((m,'unmatched provider'))
 rows.append(r)
for m in sorted(targets):visit(m)
res={'scope':'project sources for seven prefix-dependent Assembly prerequisites; Foundation and packages inherited boundaries','base':str(B),'base_state_sha256':sha(B/'state.json'),'prefix':str(D),'prefix_state_sha256':sha(D/'state.json'),'targets':sorted(targets),'rows':rows,'external_boundaries':sorted(boundary),'missing':missing,'bad':bad};out=Path(os.environ.get('ADAPTIVE_PREFIX_AUDIT_OUT','/tmp/adaptive13-assembly-prefix-audit.json'));out.write_text(json.dumps(res,indent=2)+'\n');print('inherited',len(rows),'missing',missing,'bad',bad,'cache-boundaries',[(r['module'],r['resolved_object']) for r in rows if r['provenance'].startswith('62ff')]);assert not missing and not bad
