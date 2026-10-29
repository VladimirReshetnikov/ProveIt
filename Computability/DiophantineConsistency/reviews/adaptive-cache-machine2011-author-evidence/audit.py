from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');C=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');E=Path('/tmp/adaptive13-cache-boundary-decimal-78wm7s_8');L=Path('/tmp/adaptive13-cache-boundary-light-lysi5eaz');D=Path('/tmp/adaptive13-cache-boundary-dense-ed5i1s1b');roots={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver','FirstOrder':R/'Logic/FirstOrder/Lean/FirstOrder','PAHF':R/'Logic/Interpretability/PAHF/Lean/PAHF'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
names=[('BusyBeaver','ZFC/FiniteZipper'),('BusyBeaver','ZFC/TablePerm252'),('BusyBeaver','ZFC/ArithmeticMachinePerm252'),('BusyBeaver','ZFC/ArithmeticMachineGraphPerm252'),('DiophantineConsistency','ArithmeticMachineGraph215'),('BusyBeaver','ZFC/ArithmeticMachineStepPerm252'),('DiophantineConsistency','ArithmeticMachineStep215'),('DiophantineConsistency','ArithmeticMachineRun215')];targets={ns+'.'+n.replace('/','.') for ns,n in names};ca=read('/tmp/adaptive13-assembly-composed-source-audit.json');cs=read(C/'state.json');es=read(E/'state.json');ls=read(L/'state.json');ds=read(D/'state.json');assert cs['status']==es['status']==ds['status']=='PASS' and ls['status']=='PASS_FIVE' and es['matches_previous'];a={r['module']:r for r in ca['rows']};a.update({r['namespace']+'.'+r['name'].replace('/','.'):{'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256']} for r in cs['records']});new={r['namespace']+'.'+r['name'].replace('/','.'):{'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256']} for r in ls['records']};new['BusyBeaver.ZFC.KDense215']={'source_sha256':ds['source_sha256'],'object_sha256':ds['object_sha256']};new['DiophantineConsistency.DecimalMachine215']={'source_sha256':es['source_sha256'],'object_sha256':es['object_sha256']};seen=set();rows=[];boundary=set()
def visit(m):
 if m in seen:return
 seen.add(m);ns,_,n=m.partition('.')
 if ns not in roots:boundary.add(m);return
 src=roots[ns]/(n.replace('.','/')+'.lean')
 if not src.is_file():boundary.add(m);return
 imports=[x for line in src.read_text().splitlines() if line.startswith('import ') for x in line.split('--',1)[0][7:].split()]
 for x in imports:visit(x)
 if m in targets:return
 meta=new.get(m,a.get(m));assert meta,m;old=C/'lib'/Path(m.replace('.','/')+'.olean');obj=E/'lib'/Path(m.replace('.','/')+'.olean');assert obj.is_file() and old.is_file(),m
 assert sha(src)==meta['source_sha256'] and sha(obj)==meta['object_sha256'],m
 if m not in new:assert sha(old)==meta['object_sha256'],(m,'unaffected object changed')
 rows.append({'module':m,'source':str(src),'source_sha256':sha(src),'object':str(obj),'object_sha256':sha(obj),'canonical_object_sha256':sha(old),'provenance':'new-cache-pilot' if m in new else 'accepted-composition','imports':imports})
for ns,n in names:visit(ns+'.'+n.replace('/','.'))
guards=read(C/'guards.json');assert sha(C/'guards.json')==cs['guards_sha256'];assert all(sha(p)==h for p,h in guards.items());out={'scope':'mapped project-source closure for eight machine-path rebuilds; Foundation, toolchain and package internals inherited boundaries','canonical':str(C),'canonical_state_sha256':sha(C/'state.json'),'canonical_guards_sha256':sha(C/'guards.json'),'pilot':str(E),'pilot_state_sha256':sha(E/'state.json'),'light':str(L),'light_state_sha256':sha(L/'state.json'),'dense':str(D),'dense_state_sha256':sha(D/'state.json'),'targets':sorted(targets),'rows':rows,'external_boundaries':sorted(boundary)};Path('/tmp/adaptive13-cache-machine-audit.json').write_text(json.dumps(out,indent=2)+'\n');print('inherited',len(rows),'changed pilot inputs',[r['module'] for r in rows if r['object_sha256']!=r['canonical_object_sha256']],'external',len(boundary))
