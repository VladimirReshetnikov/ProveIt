import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
REV=D/'reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
 if not c:raise RuntimeError(m)
def stripped(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
  elif depth and s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
  elif not depth and s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j<0 else j;out.extend(' '*(j-i));i=j
  else:out.append(s[i] if not depth or s[i]=='\n' else ' ');i+=1
 require(depth==0,'nested comment');return ''.join(out)
def imports(p):
 s=stripped(Path(p).read_text());out=[] if re.search(r'^\s*prelude\s*$',s,re.M) else ['Init']
 for x in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',s,re.M):out.extend(re.findall(r'[\w.]+',x))
 return list(dict.fromkeys(out))
def read(p):return json.loads(Path(p).read_text())
parents=[REV/'validator-source-full-seed222-cache.json',REV/'validator-equality-images222-cache.json',REV/'fixed-consistency73-root-replay/plan.json',REV/'fixed-consistency73-root-replay/state.json']
base,eq,old,oldstate=map(read,parents)
require(oldstate['status']=='PASS','73 not PASS')
records={}
for r in old['modules']:
 if r['action']!='reuse':continue
 records[r['module']]={**r,'source':r['source']['path'],'source_sha256':r['source']['sha256'],'provenance_parent':str(parents[2])}
for source,data in [(parents[1],eq),(parents[0],base)]:
 for r in data['modules']:records[r['module']]={**r,'provenance_parent':str(source)}
for n,provider,receipt in [
 ('ValidatorSourceFullSeed222','/tmp/validator-source-full-seed222-root-zjtprxm7/lib','validator-source-full-seed222-root'),
 ('ValidatorEqualityImages222','/tmp/validator-equality-images222-root-_3yfo2wq/lib','validator-equality-images222-root')]:
 statepath=REV/(receipt+'-replay/state.json');state=read(statepath)
 # State forms vary; find the exact execution record by its module name.
 def find(v):
  if isinstance(v,dict):
   if v.get('module')=='ZFCinPA.'+n and 'object' in v:return v
   for a in v.values():
    z=find(a)
    if z:return z
  if isinstance(v,list):
   for a in v:
    z=find(a)
    if z:return z
 r=find(state);require(r is not None,'missing root result '+n)
 p=ROOT/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA'/(n+'.lean');obj=Path(provider)/'ZFCinPA'/(n+'.olean')
 s=r['source'];s=s['sha256'] if isinstance(s,dict) else r['source_sha256']
 require(sha(p)==s,'root source '+n);require(sha(obj)==r['object']['sha256'],'root object '+n)
 records['ZFCinPA.'+n]={'module':'ZFCinPA.'+n,'source':str(p),'source_sha256':s,'objects':[{'path':str(obj),'sha256':sha(obj)}],'imports':imports(p),'provenance_parent':str(statepath),'accepted_receipt':{'path':str(REV/(receipt+'.md')),'sha256':sha(REV/(receipt+'.md'))}}
 parents.extend([statepath,REV/(receipt+'.md'),REV/(receipt+'-replay/FILES.json')])
order=[];seen=set();extnames=set()
def visit(n):
 if n in seen:return
 if n not in records:
  require(n=='Init' or n.startswith(('Mathlib.','Aesop','Lean','Std','Batteries','Qq','ImportGraph','Plausible','ProofWidgets','Cli')), 'missing custom '+n)
  extnames.add(n);return
 seen.add(n);r=records[n]
 require(sha(r['source'])==r['source_sha256'],'current source '+n)
 actual=imports(r['source']);prior=r.get('actual_imports',r.get('imports',[]))
 require(set(actual)==set(prior)|({'Init'} if 'Init' in actual else set()),'header '+n)
 r['imports']=actual
 for a in actual:visit(a)
 for o in r['objects']:require(sha(o['path'])==o['sha256'],'object '+n)
 order.append(r)
for n in ['ZFCinPA.SchemaClosure','ZFCinPA.ValidatorSourceFullSeed222','ZFCinPA.ValidatorEqualityImages222']:visit(n)
pinmap={p['path']:p['sha256'] for p in old['pins']}
externalKnown={r['module']:r for r in base['external']+eq['external']}
paths=list(dict.fromkeys((base['lean_path']+':'+old['lean_path']).split(':')))
external=[]
for n in sorted(extnames):
 if n in externalKnown:r=externalKnown[n]
 else:
  found=[Path(d)/(n.replace('.','/')+'.olean') for d in paths if (Path(d)/(n.replace('.','/')+'.olean')).is_file()]
  require(found,'missing boundary '+n);p=found[0]
  require(str(p) in pinmap,'unattested boundary '+str(p))
  r={'module':n,'path':str(p),'sha256':pinmap[str(p)],'provenance_parent':str(parents[2])}
 require(sha(r['path'])==r['sha256'],'boundary '+n);external.append(r)
obs={}
def observe(p,h=None):
 h=sha(p) if h is None else h;require(sha(p)==h,'observation '+str(p));obs[str(p)]=h
for p in parents:observe(p)
for k in ['compiler','manifest','toolchain']:observe(base[k],base[k+'_sha256'])
for r in order:
 observe(r['source'],r['source_sha256'])
 for o in r['objects']:observe(o['path'],o['sha256'])
 # Preserve selected provenance and trace records, not entire unused old closure.
 for k in ['provenance','trace','lake_trace']:
  q=r.get(k)
  if isinstance(q,dict) and 'path' in q and 'sha256' in q:observe(q['path'],q['sha256'])
for r in external:observe(r['path'],r['sha256'])
anchors=[
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeGicDelta1.lean',
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativePeel.lean',
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Ax.lean',
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeTheory.lean',
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ModelCodedBindFree.lean',
 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ModelCodedClosedSchemaAxioms.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KSeedInterface222.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerSeed.lean',
 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerRaw.lean']
for p in anchors:observe(ROOT/p)
counts={'cached_modules':len(order),'foundation':sum(r['module'].startswith('Foundation.') for r in order),'artifacts':sum(len(r['objects']) for r in order),'external_boundaries':len(external)}
result={'status':'READ_ONLY_PLAN_NO_COMPILER_OR_OVERLAY','snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'future_imports':['ZFCinPA.SchemaClosure','ZFCinPA.ValidatorSourceFullSeed222','ZFCinPA.ValidatorEqualityImages222'],'counts':counts,'modules_dependency_order':order,'external':external,'parents':[{'path':str(p),'sha256':sha(p)} for p in parents],'delta_vs_full_seed_cache':[r['module'] for r in order if r['module'] not in {q['module'] for q in base['modules']}],'observations':[{'path':p,'sha256':h} for p,h in sorted(obs.items())],'planning_driver':{'path':__file__,'sha256':sha(__file__)},'scope':'Exact source/objects rehashed read-only. No new compilation, cache mutation, or dependency refresh. Historical and Foundation provenance limitations retained.'}
out=D/'research/validator-full-seed-theory222-plan.json';require(not out.exists(),'new plan only');out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'counts':counts,'delta':result['delta_vs_full_seed_cache'],'plan':str(out),'sha256':sha(out),'observations':len(obs)},indent=2))
