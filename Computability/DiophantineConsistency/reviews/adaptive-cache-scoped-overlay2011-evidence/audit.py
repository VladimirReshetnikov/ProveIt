from pathlib import Path
import hashlib,json,os
R=Path('/home/codex/.codex/worktrees/46be/Proofs');C=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');D=Path('/tmp/adaptive13-cell-root-parent-wnvsel13');L=Path('/tmp/adaptive13-cache-boundary-light-lysi5eaz');K=Path('/tmp/adaptive13-cache-boundary-dense-ed5i1s1b');E=Path('/tmp/adaptive13-cache-boundary-decimal-78wm7s_8');M=Path('/tmp/adaptive13-cache-machine-51o9arr5');F=Path('/tmp/adaptive13-cache-frontier-future-audit.json');A=Path('/tmp/adaptive13-assembly-composed-source-audit.json');roots={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver','FirstOrder':R/'Logic/FirstOrder/Lean/FirstOrder','PAHF':R/'Logic/Interpretability/PAHF/Lean/PAHF'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
f=read(F);a=read(A);cs=read(C/'state.json');ds=read(D/'state.json');ls=read(L/'state.json');ks=read(K/'state.json');es=read(E/'state.json');ms=read(M/'state.json');assert f['status']==cs['status']==ks['status']==es['status']==ms['status']=='PASS' and ls['status']=='PASS_FIVE' and ds['status']=='FAILED';assert len(f['nodes'])==189 and len(f['future'])==15 and len(f['additional_prefix'])==12 and not f['uncovered'] and not f['affected_future'];assert ks['light_state_sha256']==sha(L/'state.json') and es['light_state_sha256']==sha(L/'state.json') and es['dense_state_sha256']==sha(K/'state.json') and ms['pilot_state_sha256']==sha(E/'state.json')
checks={}
def guard(p,h):
 p=str(p);assert p not in checks or checks[p]==h,(p,'inconsistent');checks[p]=h;assert sha(p)==h,(p,'changed')
for p,h in f['guards'].items():guard(p,h)
for p in [F,A,C/'state.json',D/'state.json',L/'state.json',K/'state.json',E/'state.json',M/'state.json']:guard(p,sha(p))
metadata={r['module']:{'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256'],'object':str(C/'lib'/Path(r['module'].replace('.','/')+'.olean'))} for r in a['rows']}
for r in cs['records']:
 m=r['namespace']+'.'+r['name'].replace('/','.');assert m not in metadata;metadata[m]={'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256'],'object':str(C/'lib'/r['namespace']/(r['name']+'.olean'))}
prefix={r['namespace']+'.'+r['name'].replace('/','.'):r for r in ds['records'][:-1]}
for m in f['additional_prefix']:
 r=prefix[m];assert m not in metadata;metadata[m]={'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256'],'object':str(D/'lib'/r['namespace']/(r['name']+'.olean'))}
assert len(metadata)==174
new={}
for r in ls['records']:
 m=r['namespace']+'.'+r['name'].replace('/','.');new[m]={'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256'],'object':str(L/'lib'/Path(m.replace('.','/')+'.olean'))}
new['BusyBeaver.ZFC.KDense215']={'source_sha256':ks['source_sha256'],'object_sha256':ks['object_sha256'],'object':str(K/'lib/BusyBeaver/ZFC/KDense215.olean')}
new['DiophantineConsistency.DecimalMachine215']={'source_sha256':es['source_sha256'],'object_sha256':es['object_sha256'],'object':str(E/'lib/DiophantineConsistency/DecimalMachine215.olean')}
for r in ms['records']:
 m=r['namespace']+'.'+r['name'].replace('/','.');new[m]={'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256'],'object':str(M/'lib'/Path(m.replace('.','/')+'.olean'))}
changed=set();matched=set()
for m,r in new.items():
 assert m in metadata and r['source_sha256']==metadata[m]['source_sha256'];guard(r['object'],r['object_sha256'])
 if r['object_sha256']==metadata[m]['object_sha256']:matched.add(m)
 else:changed.add(m)
assert sorted(changed)==f['changed'];frontiers=set(f['frontiers']);assert frontiers<=matched
selected={};edges={};future={r['module']:r for r in f['future']};boundary=set()
for m in f['nodes']:
 ns,_,n=m.partition('.');src=roots[ns]/(n.replace('.','/')+'.lean');expected=f['guards'][str(src)];guard(src,expected);im=[x for line in src.read_text().splitlines() if line.startswith('import ') for x in line.split('--',1)[0][7:].split()];edges[m]=im;boundary.update(x for x in im if x not in f['nodes'])
 if m in future:
  assert expected==future[m]['source_sha256'];continue
 old=metadata[m];guard(old['object'],old['object_sha256']);chosen=new[m] if m in changed or m in frontiers else old;guard(chosen['object'],chosen['object_sha256']);selected[m]={'source_sha256':expected,'canonical_object':old['object'],'canonical_sha256':old['object_sha256'],'selected_object':chosen['object'],'selected_sha256':chosen['object_sha256'],'choice':'rebuilt-different' if m in changed else 'rebuilt-identical-frontier' if m in frontiers else 'canonical-or-checked-prefix'}
affected=set(changed)
while True:
 before=len(affected)
 for m,im in edges.items():
  if m not in frontiers and any(x in affected for x in im):affected.add(m)
 if len(affected)==before:break
assert affected==changed and not affected.intersection(future),(sorted(affected-changed),sorted(affected.intersection(future)))
for p,h in checks.items():assert sha(p)==h,(p,'changed during audit')
out={'status':'PASS','scope':'read-only hypothetical selection for exactly 189 mapped project-source modules, with 174 existing objects and 15 unbuilt source targets; no filesystem overlay and no Lean compilation; Foundation, toolchain, packages and unmapped namespaces are boundaries','canonical':str(C),'future_audit':str(F),'changed':sorted(changed),'frontiers':sorted(frontiers),'matched':sorted(matched),'selected':selected,'unbuilt':sorted(future),'affected_outside_changed':sorted(affected-changed),'external_boundaries':sorted(boundary),'guards':checks};p=Path(os.environ.get('ADAPTIVE_SCOPED_AUDIT_OUT','/tmp/adaptive13-cache-scoped-overlay-audit.json'));p.write_text(json.dumps(out,indent=2)+'\n');print('PASS scoped sources',len(edges),'selected',len(selected),'unbuilt',len(future),'changed',len(changed),'frontiers',len(frontiers),'guards',len(checks),flush=True)
