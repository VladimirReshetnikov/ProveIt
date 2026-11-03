#!/usr/bin/env python3
"""Review the 89-to-90 model equivalence and its selected Lean producers."""
from hashlib import sha256
import json,os,re,subprocess,sys
from pathlib import Path
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];H=D/'research/ordinary12-absorb89-probe';O=H/'observations'
LIB=Path('/tmp/qcube92-halt-5apqi7f7/lib');BASE=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
PINS={BASE:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f',
 O/'chain-attempt01/result.json':'08fcb96dbafdb54208e1f0c7f6e6f0a34765d749cd0885a63caca3bd0861ca51',
 O/'growth-attempt01/terminal.json':'f08d17165973930115751cf29e33f4c8fe6b23f2c9ef7c4688efc744c972bb30',
 O/'positive-branch-attempt01/result.json':'00f19432c5b97b0c992193d6df06cc963d2f72df2c83990e11b72a3a95f3fc3a',
 O/'positive-branch-attempt02/result.json':'f026ad0f8fe68f6ad3f5c4a293753cc941aeceaf1c456b5f5db15aa326703baa',
 O/'forward-attempt01/result.json':'f60f526c80d8c79af705999c0687269df5e012bf44636add30e8bdf99fb6dbcd',
 O/'select-attempt01/result.json':'4d5ac24b98d2a0b9a705f3d66b76dd1219b881dc0a3a0d411f9fb415926b970e',
 O/'inverse-attempt01/result.json':'23625c9cdd8ee33eaa21ebd189c1dd13de29520b64829052a63931e84f30e7ff',
 O/'inverse-attempt02/result.json':'52ff61892089ceedb3ac74994eb5a8e17217112ffb3b899ded7c798774670135',
 O/'equivalence-attempt01/result.json':'6281cd65c26da3da2ca294a8e330ddae0ce99fe5ed39441ab98b808fa635489a',
 D/'reviews/ordinary12-absorb89-reflection-independent/observations/model-attempt02/terminal.json':'4f59371ac7bcabc00f7a373cdca69c66fb2b22173929ca771f9b0e2813825760',
 H/'check-dag.py':'2bdd92c36ab6f347caa9a221ed285bdc49716290ac84f8d22edca008fb842c8d'}
def need(x,m):
 if not x:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'non-file '+str(p))
 return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
for p,h in PINS.items():need(sha(p)==h,'input pin '+str(p))
base=json.loads(BASE.read_text());need(base['exit']==0 and base['union_unchanged'],'base receipt')
def inventory():
 x={p.relative_to(LIB).as_posix():rec(p) for p in LIB.rglob('*') if p.is_file()}
 need(len(x)==1291 and x==base['union'],'provider union drift');return x
before=inventory();accepted={};all_predecessors={};resource_samples=0
groups=[('chain-attempt01','run-chain.py',['Absorb89Main','Absorb89Oriented','Absorb89Indices','Absorb89Rank','Absorb89Early','Absorb89Window']),
 ('positive-branch-attempt02','run-positive-branch.py',['Absorb89PositiveBranch']),
 ('forward-attempt01','run-forward.py',['Absorb89Forward']),('select-attempt01','run-select.py',['Absorb89Select']),
 ('inverse-attempt02','run-inverse.py',['Absorb89Inverse']),('equivalence-attempt01','run-equivalence.py',['Absorb89Equivalence'])]
for name,runner,modules in groups:
 obs=O/name;d=json.loads((obs/'result.json').read_text());need(d['status']=='PASS' and sha(H/runner)==d['runner_sha256'],'runner/result '+name)
 need([r['module'] for r in d['stages']]==modules,'stage order '+name)
 roots=[Path(x) for x in d['lean_path'].split(':')]
 for path,digest in d['predecessors'].items():
  p=Path(path);need(sha(p)==digest,'predecessor drift '+path);all_predecessors[path]=digest
  first=next((root/p.name for root in roots if (root/p.name).is_file()),None)
  need(first is not None and sha(first)==digest,'top-level import shadow '+path)
 for i,row in enumerate(d['stages'],1):
  label=f'stage-{i:02}';module=row['module'];root=Path(d['output_root'])
  need(row==json.loads((obs/(label+'.json')).read_text()) and row['exit']==0 and row['reason'] is None,'stage receipt '+name)
  source=H/(module+'.lean');snapshot=obs/(label+'.source.lean');copied=root/'src'/(module+'.lean');obj=root/'lib'/(module+'.olean')
  need(sha(source)==sha(snapshot)==sha(copied)==row['source_sha256']==d['sources'][module],'source pin '+module)
  need(sha(obj)==row['object_sha256'],'output object '+module)
  so=obs/(label+'.stdout');se=obs/(label+'.stderr')
  need(sha(so)==row['stdout_sha256'] and sha(se)==row['stderr_sha256'] and not se.read_bytes(),'stage logs '+module)
  text=so.read_text();need(not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',text) and 'sorryAx' not in text,'diagnostics '+module)
  reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M)
  need(reports and all(set(x.strip() for x in a.split(','))<= {'propext','Classical.choice','Quot.sound'} for _,a in reports),'axiom reports '+module)
  pre=row['preflight'];need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean_pids'])<2,'resource preflight')
  for x in row['samples']:
   need(x['mem_available_kib']>=8*1024**2 and len(x['lean_pids'])<=2,'resource sample');resource_samples+=1
  for imported in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):
   if imported in modules:need(modules.index(imported)<i-1,'forward stage import '+module)
   if '.' not in imported:
    first=next((r/(imported+'.olean') for r in roots if (r/(imported+'.olean')).is_file()),None)
    need(first is not None,'missing selected top-level import '+imported)
  accepted[module]=row['object_sha256']
for name in ('positive-branch-attempt01','inverse-attempt01'):
 d=json.loads((O/name/'result.json').read_text());need(d['status']=='FAILED' and len(d['stages'])==1 and d['stages'][0]['exit']!=0,'failed attempt '+name)
 log=(O/name/'stage-01.stdout').read_text();need('error' in log and 'sorryAx' in log,'failure diagnostics '+name)
# Check earlier growth receipt and the independently checked full-model reflection.
growth=json.loads((O/'growth-attempt01/terminal.json').read_text());need(growth['exit']==0 and growth['reason'] is None and growth['union_unchanged'] and growth['union_count']==1291,'growth receipt')
need(sha(H/'Absorb89Growth.lean')==growth['source_sha256'] and sha(Path(growth['output_root'])/'Absorb89Growth.olean')==growth['object_sha256'],'growth source/object')
model=json.loads((D/'reviews/ordinary12-absorb89-reflection-independent/observations/model-attempt02/terminal.json').read_text())
need(model['exit']==0 and model['reason'] is None and model['union_unchanged'],'model reflection receipt')
need(sha(Path(model['output_root'])/'Absorb89ModelReflection.olean')==model['object_sha256']=='5f65eb40986de1bb580103f8c9b5682cbd12b7f4e4b40643c7e473f885559a55','model reflection object')
eq=(H/'Absorb89Equivalence.lean').read_text();positive=(H/'Absorb89PositiveBranch.lean').read_text();window=(H/'Absorb89Window.lean').read_text();select=(H/'Absorb89Select.lean').read_text();inverse=(H/'Absorb89Inverse.lean').read_text();forward=(H/'Absorb89Forward.lean').read_text()
need('(hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))' in eq,'equivalence port assumptions')
need('InternalZero (graph (integerPorts p)).output v) ↔' in eq and 'InternalZero (FreeJDirectMainGraph.graph (integerPorts p)).output v)' in eq,'equivalence graph directions')
need('Absorb89Select.select p v hb hl hh hv hz' in eq and 'Absorb89Inverse.exists_direct_of_gap' in eq and 'Absorb89Forward.exists_absorb_of_direct p' in eq,'existence composition')
need('13≤n' in window and 'theorem graph_early' in window and 'theorem graph_window' in window,'index/window claims')
need('3*v 6≤v 8+v 9' in positive and 'hBtpos' in positive and 'hsign' in positive and ': v 6<v 7' in positive,'positive branch claim')
need('negative_branch_preserves' in select and 'Absorb89PositiveBranch.positive_branch p w' in select and '∀j,0<w j' in select,'reflected selection')
need('Function.update v 7 (v 7-v 6)' in inverse and 'Function.update v 7 (v 7+v 6)' in forward,'forward/inverse maps')
run=subprocess.run([sys.executable,'-I','-S','-B',str(H/'check-dag.py')],capture_output=True,timeout=30)
need(run.returncode==0 and not run.stderr and json.loads(run.stdout)['rows']==89,'external graph check')
need(inventory()==before,'provider changed during audit')
for path,digest in all_predecessors.items():need(sha(path)==digest,'predecessor changed during audit '+path)
for p,h in PINS.items():need(sha(p)==h,'input changed during audit '+str(p))
print(json.dumps({'status':'PASS','checked_chain_modules':6,'positive_branch':accepted['Absorb89PositiveBranch'],
 'equivalence_object':accepted['Absorb89Equivalence'],'accepted_stages':len(accepted),'predecessor_files':len(all_predecessors),
 'resource_samples':resource_samples,'selected_union_files':len(before),'graph_rows':89,
 'scope':'bounded-port positive-zero equivalence in IΣ₁ models; selected project receipts; no Lean replay, full package/dynamic/source-object ancestry, halt or iPRA join'},indent=2,sort_keys=True))
