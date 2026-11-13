#!/usr/bin/env python3
"""Read-only audit of 22 protected free-J population build artifacts."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RESEARCH=BASE/'research/ordinary12-ipra-bridge';PKG=RESEARCH/'free-j-population-client-prototype'
OUT=Path('/tmp/ipra-freej-population-client-pair-02');PREFIX=Path('/tmp/ipra-freej-power-finish-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PLAN=RESEARCH/'free-j-population-closure-plan';PARENT=BASE/'reviews/ordinary12-freej-power-finish-independent-audit';WARN=BASE/'reviews/ordinary12-freej-population-warning-prelaunch-audit'
R='1bf3202710efeb892182c82a5cabcfd9ce504474e733e1dfe8c3d01e140db57c';DRIVER='ab21a262ef9ba39ba3c6dc57e1899bc8f2574231e2f1222171b547c37699d725';SEED='8070610cbaee1c035ba5a877e7c8605f42b84fd78a9a455b6a062b68f2dfc8b8'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,msg):
 if not x:raise ValueError(msg)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','d8246d0182','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()
 need(len([x for x in names if '/evidence/' in x and x.endswith('.log')])==22,'committed logs')
 for name in names:
  blob=subprocess.run(['git','show','d8246d0182:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
  need(hashlib.sha256(blob).hexdigest()==sha(ROOT/name),'committed drift '+name)
 need(sha(PKG/'replay.py')==DRIVER and sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==R,'driver/receipt')
 terminal=(PKG/'evidence/terminal.txt').read_text();need('session 11239 exit 0' in terminal and 'b28da1e6ed671e9b10a4759ac4b21e864cf91075' in terminal and terminal.rstrip().endswith('PASS_PAIRED_FREEJ_POPULATION_CLIENT '+R),'outer observation')
 rec=json.loads((PKG/'evidence/receipt.json').read_bytes());need(rec['status']=='PASS_PAIRED_FREEJ_POPULATION_CLIENT' and len(rec['runs'])==2,'receipt status')
 for path,h in rec['fixed_inputs_sha256'].items():need(sha(path)==h,'fixed pin '+path)
 need(sha(WARN/'CHECK.json')=='d2176c0ff501523446ba6cb5dbff9c20277185db6109be2affad36756103e27f','warning review pin')
 wreview=json.loads((WARN/'CHECK.json').read_bytes());need(wreview['driver_sha256']==DRIVER and wreview['status']=='PASS_CONDITIONAL_FREEJ_POPULATION_WARNING_PRELAUNCH_AUDIT','warning review status')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=900)
 need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((PARENT/'CHECK.json').read_bytes())==rec['power_audit'],'power parent audit')
 scan=json.loads((PLAN/'scan.json').read_bytes());rows=scan['preferred_rebuild'];need(len(rows)==9,'9 source closure')
 modules=[r['module'] for r in rows]+['DiophantineConsistency.FreeJPopulationFactsNarrow','DiophantineConsistency.FreeJPopulationClient']
 sourcehash={r['module']:r['source_sha256'] for r in rows};sourcehash.update({'DiophantineConsistency.FreeJPopulationFactsNarrow':rec['fixed_inputs_sha256'][str(PKG/'FreeJPopulationFactsNarrow.lean')],'DiophantineConsistency.FreeJPopulationClient':rec['fixed_inputs_sha256'][str(PKG/'FreeJPopulationClient.lean')]})
 allruns=[]
 for run,side in zip(rec['runs'],('author','peer')):
  need(run['label']==side and [s['module'] for s in run['steps']]==modules,'module order')
  lib=OUT/side/'lib';base=PREFIX/side/'lib'; orig={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')}
  extra={Path(*n.split('.')).with_suffix('.olean') for n in modules}|{Path('DiophantineConsistency/FreeJPowerFinish.olean')}
  need(len(orig)==97 and not orig&extra and actual==orig|extra,'overlay inventory')
  for rel in orig:need((lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'provider object '+str(rel))
  seed=lib/'DiophantineConsistency/FreeJPowerFinish.olean';need(sha(seed)==sha(PREFIX/side/'FreeJPowerFinish.olean')==run['power_seed_sha256']==SEED,'power seed')
  available=set(orig)|{Path('DiophantineConsistency/FreeJPowerFinish.olean')}; checked=[]
  for index,step in enumerate(run['steps']):
   name=step['module'];rel=Path(*name.split('.'));src=OUT/'frozen'/rel.with_suffix('.lean');obj=lib/rel.with_suffix('.olean');log=OUT/side/(name.replace('.','_')+'.log');copy=PKG/'evidence'/side/log.name
   need(step['compiler_exit']==step['deps_exit']==0 and step['stop_reason'] is None,'child exits '+name)
   need(sha(src)==step['source_sha256']==sourcehash[name] and sha(obj)==step['object_sha256'] and sha(log)==sha(copy)==step['log_sha256'] and log.read_text()==step['stdout'],'artifacts '+name)
   cmd=step['command'];need(cmd[1:4]==['-M3000','-j1','-DElab.async=false'] and cmd[-3]==str(src) and cmd[-1]==str(obj),'command '+name)
   imports=[v for line in src.read_text().splitlines() if line.startswith('import ') for v in line[7:].split()]
   if index<9:need(imports==rows[index]['imports'],'frozen import list')
   deps={str(PACKAGE/'Init.olean')}
   for dep in imports:
    drel=Path(*dep.split('.')).with_suffix('.olean')
    if dep.startswith('DiophantineConsistency.'):
     need(drel in available,'same-side project dependency absent at step '+name+': '+dep);candidate=lib/drel
    elif drel in available:candidate=lib/drel
    else:candidate=PACKAGE/drel
    need(candidate.is_file(),'dependency object '+dep);deps.add(str(candidate))
   need(set(step['deps_stdout'].splitlines())==deps,'direct deps '+name)
   reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",step['stdout'],re.M)
   report_names={'DiophantineConsistency.FreeJPopulationFactsNarrow':['FreeJPopulationFacts.population_of_ordinary_facts'],'DiophantineConsistency.FreeJPopulationClient':['FreeJPopulationClient.graph_population']}.get(name,[])
   need([n for n,_ in reports]==report_names and [[n,a] for n,a in reports]==step['axiom_reports'],'named reports '+name)
   need(all({x.strip() for x in ax.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,ax in reports),'axiom sets '+name)
   if name=='DiophantineConsistency.ArithmeticBinomLegendre':
    warn=f"{src}:78:10: warning: try 'simp' instead of 'simpa'\n\nNote: This linter can be disabled with `set_option linter.unnecessarySimpa false`\n";need(step['stdout']==warn,'exact allowed warning')
   else:need('warning:' not in step['stdout'],'unexpected warning '+name)
   need('error:' not in step['stdout'] and 'sorryAx' not in step['stdout'],'error/placeholder '+name)
   available.add(rel.with_suffix('.olean'));checked.append({'module':name,'source_sha256':step['source_sha256'],'object_sha256':step['object_sha256'],'recorded_compiler_exit':0,'recorded_deps_exit':0})
  allruns.append({'side':side,'steps':checked})
 need(allruns[0]['steps']==allruns[1]['steps'],'sibling objects/sources')
 print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_POPULATION_CLIENT_AUDIT','evidence_commit':'d8246d0182','receipt_sha256':R,'recorded_outer_session':11239,'recorded_outer_exit':0,'reported_launch_head':'b28da1e6ed671e9b10a4759ac4b21e864cf91075','recorded_loader_variables_removed':['LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'],'parent_audit_rerun_exit':q.returncode,'steps_per_side':11,'accepted_warning_per_side':'ArithmeticBinomLegendre.lean:78:10 unnecessarySimpa','runs':allruns,'scope':'Conditional IΣ₁-model graph population bound with positive graph zero, port bounds, p0>=46 and explicit q=2^h; no retained compact44 tuple/checker, machine or PRA proof; inherited provider and resource limitations.'},indent=2))
if __name__=='__main__':main()
