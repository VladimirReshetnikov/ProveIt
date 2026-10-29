from pathlib import Path
import hashlib,json,os
R=Path('/home/codex/.codex/worktrees/46be/Proofs');C=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');L=Path('/tmp/adaptive13-cache-boundary-light-lysi5eaz');D=Path('/tmp/adaptive13-cache-boundary-dense-ed5i1s1b');E=Path('/tmp/adaptive13-cache-boundary-decimal-78wm7s_8');M=Path(os.environ['ADAPTIVE_CACHE_MACHINE']);A=Path('/tmp/adaptive13-assembly-composed-source-audit.json');roots={'DiophantineConsistency':R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency','BusyBeaver':R/'Computability/BusyBeaver/Lean/BusyBeaver','FirstOrder':R/'Logic/FirstOrder/Lean/FirstOrder','PAHF':R/'Logic/Interpretability/PAHF/Lean/PAHF'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
cs=read(C/'state.json');ls=read(L/'state.json');ds=read(D/'state.json');es=read(E/'state.json');ms=read(M/'state.json');a=read(A);assert cs['status']==ds['status']==es['status']==ms['status']=='PASS' and ls['status']=='PASS_FIVE';assert es['matches_previous'] and a['base']==str(C) and not a['bad'] and not a['missing'];guards=read(C/'guards.json');assert sha(C/'guards.json')==cs['guards_sha256']
checks={}
def guard(p,h):
 p=str(p);assert p not in checks or checks[p]==h,(p,'inconsistent hash');checks[p]=h;assert sha(p)==h,(p,'changed')
for p,h in guards.items():guard(p,h)
for path in [C,L,D,E,M]:guard(path/'state.json',sha(path/'state.json'))
metadata={r['module']:{'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256']} for r in a['rows']}
for r in cs['records']:
 m=r['namespace']+'.'+r['name'].replace('/','.');assert m not in metadata,m;metadata[m]={'source_sha256':r['source_sha256'],'object_sha256':r['object_sha256']}
assert len(metadata)==162
nodes=set(metadata);edges={};boundary=set()
for m,r in metadata.items():
 ns,_,n=m.partition('.');src=roots[ns]/(n.replace('.','/')+'.lean');obj=C/'lib'/Path(m.replace('.','/')+'.olean');guard(src,r['source_sha256']);guard(obj,r['object_sha256']);im=[x for line in src.read_text().splitlines() if line.startswith('import ') for x in line.split('--',1)[0][7:].split()];edges[m]=[x for x in im if x in nodes];boundary.update(x for x in im if x not in nodes)
new={}
for r in ls['records']:
 m=r['namespace']+'.'+r['name'].replace('/','.');new[m]=(L/'lib'/Path(m.replace('.','/')+'.olean'),r['source_sha256'],r['object_sha256'])
new['BusyBeaver.ZFC.KDense215']=(D/'lib/BusyBeaver/ZFC/KDense215.olean',ds['source_sha256'],ds['object_sha256'])
new['DiophantineConsistency.DecimalMachine215']=(E/'lib/DiophantineConsistency/DecimalMachine215.olean',es['source_sha256'],es['object_sha256'])
for r in ms['records']:
 m=r['namespace']+'.'+r['name'].replace('/','.');new[m]=(M/'lib'/Path(m.replace('.','/')+'.olean'),r['source_sha256'],r['object_sha256'])
changed=set();matched=set()
for m,(obj,src_hash,obj_hash) in new.items():
 assert m in metadata,m;assert src_hash==metadata[m]['source_sha256'];guard(obj,obj_hash)
 if obj_hash==metadata[m]['object_sha256']:matched.add(m)
 else:changed.add(m)
expected_changed={'BusyBeaver.Core','BusyBeaver.ZFC.KZip','BusyBeaver.ZFC.KDenseBridge','BusyBeaver.ZFC.KTableCore','BusyBeaver.ZFC.KTable215','BusyBeaver.ZFC.KDense215','BusyBeaver.ZFC.FiniteZipper'};frontiers={'DiophantineConsistency.DecimalMachine215','BusyBeaver.ZFC.TablePerm252','BusyBeaver.ZFC.ArithmeticMachinePerm252'};assert changed==expected_changed and frontiers<=matched,(changed,matched)
affected=set(changed)
while True:
 before=len(affected)
 for m in nodes:
  if m not in frontiers and any(d in affected for d in edges[m]):affected.add(m)
 if len(affected)==before:break
uncovered=sorted(affected-changed);targets={r['namespace']+'.'+r['name'].replace('/','.') for r in cs['records']};assert not uncovered and not (affected&targets),(uncovered,affected&targets)
for p,h in checks.items():assert sha(p)==h,(p,'changed during audit')
out={'status':'PASS','scope':'read-only propagation over 162 mapped project-source modules of the 40 recorded composition outputs; conditional byte-identical frontiers; no replacement overlay and unmapped/Foundation/toolchain/package internals remain boundaries','canonical':str(C),'machine_replay':str(M),'nodes':sorted(nodes),'target_count':len(targets),'changed':sorted(changed),'matched':sorted(matched),'frontiers':sorted(frontiers),'frontier_changed_inputs':{m:[x for x in edges[m] if x in changed] for m in sorted(frontiers)},'uncovered':uncovered,'affected_targets':sorted(affected&targets),'external_boundaries':sorted(boundary),'guards':checks};p=Path(os.environ.get('ADAPTIVE_FRONTIER_AUDIT_OUT','/tmp/adaptive13-cache-frontier-audit.json'));p.write_text(json.dumps(out,indent=2)+'\n');print('PASS mapped',len(nodes),'changed',len(changed),'matched',len(matched),'uncovered',len(uncovered),'affected targets',len(affected&targets),'guards',len(checks),flush=True)
