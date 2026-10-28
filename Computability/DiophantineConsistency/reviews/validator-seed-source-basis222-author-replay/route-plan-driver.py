import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency';REV=D/'reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
 if not c:raise RuntimeError(m)
def read(p):return json.loads(Path(p).read_text())
def stripped(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
  elif depth and s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
  elif not depth and s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  else:out.append(s[i] if not depth or s[i]=='\n' else ' ');i+=1
 require(depth==0,'comment');return ''.join(out)
def imports(p):
 s=stripped(Path(p).read_text());out=[] if re.search(r'^\s*prelude\s*$',s,re.M) else ['Init']
 for x in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M):out.extend(re.findall(r'[\w.]+',x))
 return list(dict.fromkeys(out))
basep=REV/'validator-full-seed-theory222-cache.json'
oldp=REV/'fixed-consistency73-root-replay/plan.json'
statep=REV/'fixed-consistency73-root-replay/state.json'
peerp=REV/'validator-full-seed-theory222-peer-replay.json'
base,old,state,peer=map(read,[basep,oldp,statep,peerp])
require(state['status']=='PASS' and peer['status']=='PASS','parent not PASS')
parents=[basep,oldp,statep,peerp,REV/'validator-full-seed-theory222-root.md',REV/'validator-full-seed-theory222-root-auth/FILES.json']
fresh={r['module']:r for r in state['completed']}
records={}
for r in old['modules']:
 q={**r,'source':r['source']['path'],'source_sha256':r['source']['sha256'],'provenance_parent':str(oldp)}
 if r['action']=='fresh':
  e=fresh[r['module']];require(e['exit_code']==0,'old fresh failure')
  require(e['source']==r['source'],'old fresh source')
  q['objects']=[e['object']];q['provenance_parent']=str(statep);q['execution_record']=e
 records[r['module']]=q
for r in base['modules']:records[r['module']]={**r,'provenance_parent':str(basep)}
pr=next(r for r in peer['records'] if r['module']=='ZFCinPA.ValidatorFullSeedTheory222')
src=ROOT/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorFullSeedTheory222.lean'
sh=pr['source']['sha256'] if isinstance(pr['source'],dict) else pr['source_sha256']
records[pr['module']]={'module':pr['module'],'source':str(src),'source_sha256':sh,
 'objects':[pr['object']],'imports':imports(src),'provenance_parent':str(peerp),
 'accepted_receipt':str(REV/'validator-full-seed-theory222-root.md')}
knownext={r['module']:r for r in base['external']}
oldpins={p['path']:p['sha256'] for p in old['pins']}
paths=list(dict.fromkeys((base['lean_path']+':'+old['lean_path']).split(':')))
observed={}
def observe(p,h=None):
 p=str(p);h=sha(p) if h is None else h;require(sha(p)==h,'hash '+p);observed[p]=h
def closure(targets):
 order=[];seen=set();names=set()
 def visit(n):
  if n in seen:return
  if n not in records:
   require(n=='Init' or n.startswith(('Mathlib.','Aesop','Lean','Std','Batteries','Qq','ImportGraph','Plausible','ProofWidgets','Cli')),'missing custom '+n)
   names.add(n);return
  seen.add(n);r=records[n];observe(r['source'],r['source_sha256'])
  actual=imports(r['source']);prior=r.get('actual_imports',r.get('imports',[]))
  require(set(actual)==set(prior)|({'Init'} if 'Init' in actual else set()),'header '+n)
  r={**r,'imports':actual}
  for x in actual:visit(x)
  for o in r['objects']:observe(o['path'],o['sha256'])
  for k in ['provenance','trace','lake_trace']:
   x=r.get(k)
   if isinstance(x,dict) and 'path' in x and 'sha256' in x:observe(x['path'],x['sha256'])
  order.append(r)
 for t in targets:visit(t)
 ext=[]
 for n in sorted(names):
  if n in knownext:r=knownext[n]
  else:
   matches=[Path(d)/(n.replace('.','/')+'.olean') for d in paths if (Path(d)/(n.replace('.','/')+'.olean')).is_file()]
   require(matches,'missing external '+n);p=matches[0]
   require(str(p) in oldpins,'external unpinned '+str(p))
   r={'module':n,'path':str(p),'sha256':oldpins[str(p)],'provenance_parent':str(oldp)}
  observe(r['path'],r['sha256']);ext.append(r)
 return {'imports':targets,'counts':{'cached_modules':len(order),'foundation':sum(r['module'].startswith('Foundation.') for r in order),'artifacts':sum(len(r['objects']) for r in order),'external_boundaries':len(ext)},'modules_dependency_order':order,'external':ext,
 'delta_vs_accepted_full_seed_theory_inputs':[r['module'] for r in order if r['module'] not in {x['module'] for x in base['modules']}]}
branches={}
targets=['ZFCinPA.ValidatorFullSeedTheory222','ZFCinPA.ModelCodedOpenSchemaAxioms']
branches['recommended_seed_open_basis']=closure(targets)
branches['later_parameterized_finite_templates']=closure(targets+['ZFCinPA.OpenTemplateClosure'])
branches['later_internal_marker_transport_candidates']=closure(targets+['ZFCinPA.InternalInterpretation','ZFCinPA.ModelCodedProofRenaming'])
anchors=[
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LSchema.lean',
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeTheory.lean',
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeInterp.lean',
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeFixed.lean',
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeSchema.lean',
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeWFClosedParameters.lean',
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NTemplate.lean',
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/Translation.lean',
 'Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/ModelCodedPredicateParameters.lean',
 'Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/InternalRelativization.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedInterface222.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerSeed.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerRaw.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerRel.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerTag.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerEqv.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerQHyp.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQHyp.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ZF.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Model.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1Collect.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ReplacementNative.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileCollection.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ProfileModel.lean',
 '/home/codex/src/Proofs/lib/FormalizedFormalLogic-Foundation/Foundation/FirstOrder/Interpretation.lean']
for p in anchors:observe(ROOT/p)
for n in ['ZFCinPA.LSchema','ZFCinPA.NativeSchema','ZFCinPA.InternalInterpretation']:
 r=records[n];observe(r['source'],r['source_sha256'])
 for o in r['objects']:observe(o['path'],o['sha256'])
for p in parents:observe(p)
for k in ['compiler','manifest','toolchain']:observe(base[k],base[k+'_sha256'])
result={'status':'READ_ONLY_PLAN_NO_COMPILER_OR_OVERLAY','snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
 'branches':branches,'selected_full_seed_provider':records['ZFCinPA.ValidatorFullSeedTheory222'],
 'tail_contract_providers':{n:records[n] for n in ['ZFCinPA.LSchema','ZFCinPA.NativeSchema','ZFCinPA.InternalInterpretation']},
 'parents':[{'path':str(p),'sha256':sha(p)} for p in parents],
 'anchor_sources':[{'path':str(ROOT/p),'sha256':sha(ROOT/p)} for p in anchors],
 'observations':[{'path':p,'sha256':h} for p,h in sorted(observed.items())],
 'planning_driver':{'path':__file__,'sha256':sha(__file__)},
 'scope':'Source/header/object/provenance rehash only. No compiler, overlay creation, dependency refresh, or shared mutation. Alternate later branches are import feasibility inventories, not accepted proof plans. Historical absent-companion and prior trace qualifications retained; no whole closure freshly checked claim.'}
out=D/'research/validator-seed-tagged-interpretation-plan.json';require(not out.exists(),'new plan only');out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'plan':str(out),'sha256':sha(out),'counts':{k:v['counts'] for k,v in branches.items()},'observations':len(observed)},indent=2))
