"""Owned source-only P23 closure derivation; never invokes Lean or supplied producers.

The explicit spec lists changed sources and separately preserved retirements. Virtual mode
checks old canonical bytes; --require-adopted checks final canonical bytes and absences.
"""
from pathlib import Path
import argparse,hashlib,json,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
B=Path('/tmp/k215-phase22-check-v3/candidate-build-run1')
P=Path('/tmp/k215-phase22-check-v3/candidate-plan.json')
BASIS_SHA='cd966bd654b04a3c2becbafc00ba1f13f2866fcbab64b5b6715cf6449461dc66'
RUNNER_SHA=P23_RUNNER_SHA
BASE_COMMIT='017861249e7da624c007e0dd6d170e32433be549'
ROOTS=['Computability/BusyBeaver/Lean','Logic/FirstOrder/Lean','SetTheory/ZF/Lean','SetTheory/BoundedConsistency/Lean']
LEAF=['README.md','capture-config.json','capture.json','capture.py','check-plan.json','check.py','evidence.tar.gz','index.json','result-review.json','result.json','review_actual.py']
STD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def clean(t):
 out=[];i=0;depth=0
 while i<len(t):
  if t[i:i+2]=='/-':depth+=1;i+=2
  elif depth and t[i:i+2]=='-/':depth-=1;i+=2
  elif depth:
   if t[i]=='\n':out.append('\n')
   i+=1
  elif t[i:i+2]=='--':
   j=t.find('\n',i);i=len(t)if j<0 else j
  elif t[i]=='"':
   i+=1
   while i<len(t):
    if t[i]=='\\':i+=2
    elif t[i]=='"':i+=1;break
    else:i+=1
  else:out.append(t[i]);i+=1
 assert depth==0;return ''.join(out)
def imports(p):return[x for line in re.findall(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)',clean(p.read_text()))for x in line.split()]
def profiles(t):return[[n,sorted({x.strip()for x in ax.split(',')if x.strip()})]for n,ax in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",t)]
def save(p,x):
 with Path(p).open('x')as f:json.dump(x,f,indent=2);f.write('\n')
parser=argparse.ArgumentParser()
for name in ['source-spec','runner','out']:parser.add_argument('--'+name,type=Path,required=True)
parser.add_argument('--source-spec-sha',required=True);parser.add_argument('--extra-pin',nargs=2,action='append',default=[]);parser.add_argument('--require-adopted',action='store_true');args=parser.parse_args()
assert sha(args.source_spec)==args.source_spec_sha and sha(args.runner)==RUNNER_SHA and sha(B/'result.json')==BASIS_SHA
result=read(B/'result.json');inventory=read(B/'inventory.json');done=read(B/'completed.json');prior=read(P)
assert result['status']=='PASS'and len(done)==len(inventory['modules'])==226
assert sha(B/'inventory.json')==result['inventory_sha256']and sha(B/'completed.json')==result['completed_sha256']and sha(P)==result['map_sha256']
historical={r['module']:r for r in inventory['modules']};oldrows={r['module']:r for r in prior['modules']};assert len(historical)==226 and set(oldrows)==set(historical)
clients={m:r for m,r in historical.items()if not m.startswith(('BusyBeaver.','FirstOrder.','ZF.','BoundedZFCConsistency.'))};assert len(clients)==15
spec=read(args.source_spec);sources={r['module']:r for r in spec['sources']};assert len(sources)==len(spec['sources'])and sources
retired_rows=spec.get('retired_modules',[]);retired_new={r['module']:r for r in retired_rows};assert len(retired_new)==len(retired_rows)and not(set(retired_new)&set(sources))
retired=set(prior['retired_modules'])|set(retired_new)
for m,r in sources.items():
 assert sha(r['candidate']['path'])==r['candidate']['sha256'],m
 canonical=Path(r['canonical']);assert any(canonical==R/root/(m.replace('.','/')+'.lean')for root in ROOTS)
 if r['before']:assert m in historical and sha(r['before']['path'])==r['before']['sha256']==historical[m]['source_sha256'],m
 else:assert m not in historical
 if args.require_adopted:assert sha(canonical)==r['candidate']['sha256'],m
 elif r['before']:assert sha(canonical)==r['before']['sha256'],m
 else:assert not canonical.exists()and not canonical.is_symlink()
for m,r in retired_new.items():
 assert m in historical and sha(r['snapshot'])==r['sha256']==historical[m]['source_sha256']and r['canonical']==historical[m]['source'],m
 if args.require_adopted:assert not Path(r['canonical']).exists()and not Path(r['canonical']).is_symlink()
 else:assert sha(r['canonical'])==r['sha256']
actual_reports={}
for m,r in done.items():
 assert r['status']=='PASS'and r.get('exit_code',0)==0 and not r.get('timed_out',False)
 source=B/'workspace'/(m.replace('.','/')+'.lean');assert sha(source)==historical[m]['source_sha256']==r['source_sha256']and source.stat().st_size==historical[m]['bytes']
 assert sha(r['log'])==r['log_sha256'];text=Path(r['log']).read_text();assert 'error:'not in text and 'sorryAx'not in text
 actual_reports[m]=profiles(text)
 assert actual_reports[m]==oldrows[m]['expected_reports']and all(set(ax)<=STD for _,ax in actual_reports[m])
assert sum(len(actual_reports[m])for m in clients)==93 and len(actual_reports['BusyBeaver.ZFC.WFTheory'])==5
assert len(prior['audits'])==2 and sum(len(a['expected_reports'])for a in prior['audits'])==10
rows=[];selected={};seen=set();active=set()
def current_source(m):
 if m in clients:return Path(clients[m]['source'])
 if m in sources:return Path(sources[m]['canonical'])
 found=[R/root/(m.replace('.','/')+'.lean')for root in ROOTS if(R/root/(m.replace('.','/')+'.lean')).is_file()]
 assert len(found)==1,(m,found);return found[0]
def visit(m):
 if m=='Init'or m in seen:return
 assert m not in active and m not in retired,m;active.add(m)
 canonical=current_source(m);virtual=Path(sources[m]['candidate']['path'])if m in sources else canonical;imps=imports(virtual)
 if m not in sources:assert m in historical and sha(virtual)==historical[m]['source_sha256']and imps==historical[m]['imports'],m
 for d in imps:visit(d)
 row={'module':m,'source':str(canonical),'source_sha256':sha(virtual),'bytes':virtual.stat().st_size,'lines':len(virtual.read_text().splitlines()),'imports':imps,'expected_reports':actual_reports.get(m,[])}
 if oldrows.get(m,{}).get('warnings_forbidden')or m in sources:row['warnings_forbidden']=True
 active.remove(m);seen.add(m);rows.append(row);selected[m]=row
for m in prior['targets']:visit(m)
assert not(set(selected)&retired)and set(clients)<=set(selected)and set(sources)<=set(selected)
changed={m for m,r in selected.items()if m not in historical or(r['source_sha256'],r['imports'])!=(historical[m]['source_sha256'],historical[m]['imports'])};assert changed==set(sources)
forced=set(changed)
while True:
 more=forced|{m for m,r in selected.items()if set(r['imports'])&forced}
 if more==forced:break
 forced=more
affected_clients=sorted(set(clients)&forced)
for m in forced:selected[m]['warnings_forbidden']=True
present={}
def pin(p,expected=None):
 p=Path(p);actual=sha(p)
 if expected is not None:assert actual==expected,p
 present[str(p.resolve())]=actual
for p,h in P23_RUNTIME_INPUTS.items():pin(p,h)
for r in sources.values():
 pin(r['candidate']['path'],r['candidate']['sha256'])
 if r['before']:pin(r['before']['path'],r['before']['sha256'])
for p,h in spec.get('static_inputs',{}).items():pin(p,h)
for p,h in args.extra_pin:pin(p,h)
for p in [args.source_spec,args.runner,Path(__file__).resolve()]:pin(p)
packet=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase22/lean'
for n in LEAF:pin(packet/n)
assert sha(packet/'result.json')==BASIS_SHA
for n in['k215.tm','k215.native.tm','sites215.json']:
 p=R/'Computability/BusyBeaver/Research/ZFC/candidate-k215'/n;pin(p,prior['present_inputs'][str(p)])
p=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/generate_l2dom.py';pin(p,prior['present_inputs'][str(p)])
absent=list(prior['absent_inputs']);assert len(absent)==16
for p in absent:assert not Path(p).exists()and not Path(p).is_symlink()
retirements=retired_rows+spec.get('retired_producers',[])
for r in retirements:
 pin(r['snapshot'],r['sha256']);p=Path(r['canonical']);assert str(p)not in absent;absent.append(str(p))
 if args.require_adopted:assert not p.exists()and not p.is_symlink()
 else:assert sha(p)==r['sha256']
assert len(absent)==len(set(absent))==16+len(retirements)
for a in prior['audits']:pin(a['source'],a['source_sha256'])
def closure(table,target):
 names=set()
 def walk(m):
  if m=='Init'or m in names:return
  names.add(m)
  for d in table[m]['imports']:walk(d)
 walk(target);return names
oldend=closure(historical,'BusyBeaver.ZFC.KEndpoint215');newend=closure(selected,'BusyBeaver.ZFC.KEndpoint215')
metrics={'old_module_count':len(oldend),'old_source_bytes':sum(historical[m]['bytes']for m in oldend),'new_module_count':len(newend),'new_source_bytes':sum(selected[m]['bytes']for m in newend),'added_modules':sorted(newend-oldend),'removed_modules':sorted(oldend-newend)}
assert(metrics['old_module_count'],metrics['old_source_bytes'])==(prior['endpoint_closure']['new_module_count'],prior['endpoint_closure']['new_source_bytes'])
expected={'provider_count':len(rows),'project_count':len(rows)-len(clients),'typed_client_count':len(clients),'affected_typed_clients':affected_clients,'changed_sources':sorted(changed),'fresh_by_source_transitivity':sorted(forced)}
plan={'status':'SOURCE_DERIVED_READY_FOR_ROOT_REVIEW'if args.require_adopted else'SOURCE_DERIVED_VIRTUAL_CANDIDATE_NOT_YET_ADOPTED','base_commit':BASE_COMMIT,'main_commit':prior['main_commit'],'mode':'phase23-candidate','basis_directory':str(B),'basis_result_sha256':BASIS_SHA,'targets':prior['targets'],'modules':rows,'audits':prior['audits'],'retired_modules':sorted(retired),'absent_inputs':absent,'present_inputs':present,'expected':expected,'source_overlay':spec['sources'],'newly_retired_module_sources':retired_rows,'newly_retired_producers':spec.get('retired_producers',[]),'unselected_old_modules':sorted(set(historical)-set(selected)),'endpoint_closure':metrics,'scope':'One exact source-transitive closure of all accepted phase22 targets and fifteen maintained clients. Every forced provider is warning-free. All report profiles come from accepted phase22 logs; new modules have empty profiles. Two endpoint audits remain fresh. No claim for an internal PA endpoint or other machine variants.'}
save(args.out,plan)
print(json.dumps({'status':plan['status'],'plan':str(args.out),'sha256':sha(args.out),'providers':len(rows),'project':len(rows)-len(clients),'clients':len(clients),'affected_clients':affected_clients,'changed':len(changed),'fresh':len(forced),'reuse':len(rows)-len(forced),'audits':len(plan['audits']),'present_inputs':len(present),'absent_inputs':len(absent),'retired_Lean_modules':sorted(retired_new),'endpoint':metrics,'compiler_invocations':0},indent=2))
