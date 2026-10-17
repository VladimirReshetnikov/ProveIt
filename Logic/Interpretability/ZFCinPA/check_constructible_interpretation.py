"""Consolidated fixed constructible interpretation, ordinary relativization and finite L axioms.
Only the new source and focused audit are compiled. Prepare-only invokes neither
Lean nor a version query. Arbitrary internal Separation/Replacement proofs remain open.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,sys,time
sys.dont_write_bytecode=True
MODULE='ZFCinPA.ConstructibleInterpretation'
SOURCE_SHA='965a7e999b810337fcd5278aa3569c430cd5311edff969995a69106e4eccf007'
AUDIT_SHA='8d6ba022a50bb31a9db31aa42919570160ad217c6aa392a6aca320c79319e0bf'
CORE_SHA='e02e4cbac881f97bc59b6d5681209e358af702e7a9b8f95cb9bbc7c061b0d5e7'
SET_SHA='2a235367a454a23c709bce36e924c11d7a23e55394d7aef6eb314b17143dfc4e'
REL_SHA='83534a1aeeeaa97881e4632156cad75120be730bd7d77761d3e460e87a4fca55'
HELPER_SHA='9a8d4d7dd467ac8152238c8a0cbe93ed87512be36b447e38bae0b8244a28b229'
COMPILER_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
D1='Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1'
BOUNDARIES={
 'Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic':('72e3cf386967e3fed4366ee5aa59678a0333cd2f40c8dbb09bebbf8dd4fa80e3','c46f491eded2b033f450406537c1e02b6135a6b563f18a6cac1589f535ad5b69'),
 D1:('36dad6e5b68427eb3e23320db4c3a6891900fe1582a6ccd4eefd60bb83eaa46e','bd2bb4fcb30f74b67efd9b12d5c9e56ebadd4192cf59997340547f09d9c9cba3'),
 'Foundation.FirstOrder.Bootstrapping.Syntax':('18257680a6f1d84b6b4ae3d6dc5c07f4adcd4aa660fe3d4f63fa4df98932c79c','7eecf0d4bf8fd67fd59dba66deb007a78da940367d3e3b932f5a6f19eb14a23c'),
 'Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1':('4c87d00022da1dd0b75b3d73e184d04458835f362dcdda06e5529574ce2b99cf','5951b3610954e29c7de0bf2335ef7e3624a7e4c566f30eff6fb9b9d6ea6371a6'),
 'Foundation.FirstOrder.SetTheory.Basic.Axioms':('9952df1012c4eeb08eb2f40b1719a1912856ce013daec5735a9ac81a97f4c9b8','e2654fef89ea6d605dbb52b87ad19d2b9e98ed3c532f6d3145689d404d5f0704')}
ANCHORS={
 'Foundation.FirstOrder.Arithmetic.IOpen.Basic':('4ec52a7a487aeafb0e9ea10716452b34f138d8214ad5a1aa5466064d6a4c9d7b','b43eb2f8d8a2ef18004125594adafbff02b52f1b6ef62b9b836015bdce2351ad'),
 'Mathlib.Tactic.Ring':('d3ef5c49ebbd1108ce3f935e5ad95485e143abf02f28c027dba4bb6f3be8196e','cc12dfa66db7ef6ae4cd2d7a4e035ddffaca827168243f728812776b77836eb4')}
TOOLS={'Init':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e','Lean':'1c099f2b3587535ed451498b40390f140751d66760f5831dfe92ecd198968e74','Std':'47c15fd871e3e77f25ed908e07c0914aa52b8abec810c728e2a152598e7f7644','Lean.Elab.Tactic.Omega':'eb766bae1ab40110a853c7cca853e36e1f4aece010a09fa4dd9b1b48116953fe'}
PROJECTS=set('''BoundedPAConsistency.InternalRelativization BoundedZFCConsistency.Basic BoundedZFCConsistency.Choice BoundedZFCConsistency.CodePredicate BoundedZFCConsistency.Coding BoundedZFCConsistency.FormulaClosedSet BoundedZFCConsistency.InternalSat BoundedZFCConsistency.InternalSatTotality BoundedZFCConsistency.OmegaRecursion BusyBeaver.ZFC.CodeOrder BusyBeaver.ZFC.Constructible BusyBeaver.ZFC.ConstructibleAbs BusyBeaver.ZFC.ConstructibleDef BusyBeaver.ZFC.ConstructibleOrder BusyBeaver.ZFC.ConstructibleReflect BusyBeaver.ZFC.ConstructibleZF BusyBeaver.ZFC.InternalOrd BusyBeaver.ZFC.InternalRank BusyBeaver.ZFC.InternalWO BusyBeaver.ZFC.NamedZF BusyBeaver.ZFC.OrderRec BusyBeaver.ZFC.SatSupport BusyBeaver.ZFC.TransRec BusyBeaver.ZFC.TupleOrder BusyBeaver.ZFC.ZFRank FirstOrder.Calculus FirstOrder.Completeness FirstOrder.Fol ZF.Zf ZFCinPA.Instances ZFCinPA.NativeZFContainers254 ZFCinPA.ReplacementDelta1 ZFCinPA.SchemaClosure ZFCinPA.SeparationDelta1 ZFCinPA.SetRelativization ZFCinPA.ZFDelta1'''.split())
IMPORTS=['ZFCinPA.NativeZFContainers254',D1,'ZFCinPA.ZFDelta1','ZFCinPA.SetRelativization','BusyBeaver.ZFC.ConstructibleOrder']
NAMES=['inLSyn_eq', 'sat_inLForm', 'eval_domL', 'eval_domAt', 'eval_relF', 'models_relF_iff', 'modelsZ_of_modelsZF', 'repl_clauseZF', 'zfAxioms_of_modelsZF', 'power_of_modelsZF', 'regular_of_modelsZF', 'inLV_nonempty', 'L_models', 'zf_proves_relL', 'zf_proves_exists_L', 'quote_domAt', 'quote_relF', 'quote_relF_sentence', 'isSemiformula_quote_domL', 'shift_quote_domL', 'provable_exists_L', 'mem_ZFC_class', 'standard_of_mem_class', 'standard_obligation', 'provable_falsum_ZF_of_ZFC']
PREFIX='LeanProofs.ZFCinPA.ConstructibleInterpretation.'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise RuntimeError(msg)
def rel(m,suffix):return Path(m.replace('.','/')).with_suffix(suffix)
def main():
 p=argparse.ArgumentParser(description=__doc__)
 for k in ['repo','dependency-root','output']:p.add_argument('--'+k,type=Path,required=True)
 for k in ['source','audit','core-evidence','set-evidence','relativization-evidence','cache','namespace-cache','lean']:p.add_argument('--'+k,type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[])
 p.add_argument('--prepare-only',action='store_true');p.add_argument('--timeout-seconds',type=int,default=120);a=p.parse_args()
 if not __debug__:p.error('Python -O is unsupported: identity guards must remain enabled.')
 req(1<=a.timeout_seconds<=300,'Timeout must be between 1 and 300 seconds.')
 R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve();Z=R/'Logic/Interpretability/ZFCinPA'
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or(W.is_dir()and not any(W.iterdir()))),'Fresh external output required.')
 S=(a.source or Z/'Lean'/rel(MODULE,'.lean')).resolve();A=(a.audit or Z/'Lean/ZFCinPA/ConstructibleInterpretationFocusedAudit.lean').resolve()
 req((sha(S),sha(A))==(SOURCE_SHA,AUDIT_SHA),'Changed frozen source/audit.')
 E=(a.core_evidence or R/'Computability/BusyBeaver/Research/ZFC/results/command-word254-integration-verification.json').resolve();G=(a.set_evidence or Z/'results/model-coded-decoder-collection254-verification.json').resolve()
 F=(a.relativization_evidence or R/'Computability/BusyBeaver/Research/ZFC/results/internal-relativization-refresh-verification.json').resolve()
 req((sha(E),sha(G),sha(F))==(CORE_SHA,SET_SHA,REL_SHA),'Wrong exact existing provider records.')
 e=json.loads(E.read_text());g=json.loads(G.read_text());f=json.loads(F.read_text())
 req(f['status']=='PASS'and(f['named_axiom_probes'],f['callers'])==(19,24)and f['only_standard_axioms']and f['all_input_provider_postchecks']and f['all_fresh_objects_unchanged_after_audit'],'Wrong fresh827+Set50 PASS contract.')
 req({q['module']:q['source_sha256']for q in f['sources']}=={'BoundedPAConsistency.InternalRelativization':'a64c5e65dd235068fb1d62d8e82be55a6f325375d081663fa8dc2a946e2ad11a','ZFCinPA.SetRelativization':'b2d4cec4106aa5ff68a66b1b624415b4ec91f8bcb542340716b83d1f3eadfdae'},'Wrong exact relativization source pair.')
 req(e['status']=='PASS169-unit source-verified integration'and e['units']==169 and e['only_standard_axioms']and e['audit']['exit_code']==0 and e['all_source_identities_unchanged_after_check']and e['all_object_identities_unchanged_after_check']and e['all_reused_object_identities_unchanged_after_check']and all(q['exit_code']==0 for q in e['fresh_checks']),'Wrong native169 PASS contract.')
 req(g['status']=='PASS'and(g['named_axiom_probes'],g['callers'])==(10,16)and g['only_standard_axioms']and g['all_input_provider_postchecks']and g['all_fresh_objects_unchanged_after_audit'],'Wrong actual G PASS contract.')
 req((g['source']['sha256'],g['audit']['sha256'])==('64a133445dde69c2e642ab6397c2b72c51bd025f2843412a9d5bc8a8c2eeaa3e','a9798acde4a76cdf640fbb3bed348c5824dfbc5fe87c51eef24ab2605d117544'),'Wrong historical G source/audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';req(sha(helper)==HELPER_SHA,'Changed discovery helper.')
 sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C=(a.lean or Path(g['compiler']['path'])).expanduser().resolve();req(sha(C)==e['compiler']['sha256']==g['compiler']['sha256']==f['compiler']['sha256']==COMPILER_SHA,'Different compiler binary.')
 version=g['compiler']['version'];req(version==e['compiler']['version']==f['compiler']['version']and version.startswith('Lean (version 4.32.0,'),'Different recorded compiler.')
 if not a.prepare_only:req(subprocess.check_output([str(C),'--version'],text=True).strip()==version,'Different observed compiler version.')
 libs,deps=H.dependency_libraries(D,a.library_path)
 for n in ['Foundation','Mathlib']:req(deps[n]['pin']==g['dependencies'][n]['pin']and deps[n]['tracked_clean']and g['dependencies'][n]['tracked_clean'],'Different dependency pin/tracked state.')
 req(deps['lake_manifest_sha256']==g['dependencies']['lake_manifest_sha256'],'Different dependency manifest.')
 for m,q in deps['providers'].items():req(q['sha256']==g['dependencies']['providers'][m]['sha256'],'Different discovery anchor '+m)
 pool={}
 for q in e['source_closure']:
  pool[q['module']]=dict(module=q['module'],source=str(R/q['path']),source_sha256=q['sha256'],object=q['olean'],object_sha256=q['olean_sha256'],evidence=str(E))
 for q in g['reused_modules']:
  m=q['module']
  if m in pool:req((q['source_sha256'],q['object_sha256'])==(pool[m]['source_sha256'],pool[m]['object_sha256']),'Conflicting exact shared project '+m)
  rr=Path(pool[m]['source']).relative_to(R)if m in pool else Path('Logic/Interpretability/ZFCinPA/Lean')/rel(m,'.lean')if m.startswith('ZFCinPA.')else Path('Computability/BusyBeaver/Lean')/rel(m,'.lean')
  if m=='FirstOrder.Fol':rr=Path('Logic/FirstOrder/Lean')/rel(m,'.lean')
  pool[m]=dict(q,source=str(R/rr),evidence=str(G))
 for fresh in f['fresh_modules']:
  m=fresh['module'];root=R/('Logic/PeanoArithmetic/BoundedConsistency/Lean'if m.startswith('BoundedPAConsistency.')else'Logic/Interpretability/ZFCinPA/Lean')
  if m in pool:req(pool[m]['source_sha256']==fresh['source_sha256'],'Conflicting refreshed source '+m)
  pool[m]=dict(module=m,source=str(root/rel(m,'.lean')),source_sha256=fresh['source_sha256'],object=fresh['path'],object_sha256=fresh['sha256'],evidence=str(F))
 selected={}
 for m in sorted(PROJECTS):
  req(m in pool,'Missing exact project '+m);q=dict(pool[m])
  if a.cache:q['object']=str(a.cache.resolve()/rel(m,'.olean'))
  req((sha(q['source']),sha(q['object']))==(q['source_sha256'],q['object_sha256']),'Changed project source/object '+m);selected[m]=q
 req(H.lean_imports(S.read_text())==IMPORTS and H.lean_imports(A.read_text())==[MODULE],'Different exact source/audit imports.')
 seen=set();external=set();visiting=set()
 def visit(m):
  if m in seen:return
  req(m in selected and m not in visiting,'Missing or circular project '+m);visiting.add(m)
  for n in H.lean_imports(Path(selected[m]['source']).read_text()):
   if n in selected:visit(n)
   else:req(n.startswith(('Foundation.','Mathlib.','Lean.','Std.'))or n in {'Init','Std','Lean'},'Unattested project import '+n);external.add(n)
  visiting.remove(m);seen.add(m)
 for m in IMPORTS:
  if m in selected:visit(m)
  else:external.add(m)
 is_tool=lambda m:m in {'Init','Lean','Std'}or m.startswith(('Lean.','Std.'))
 req(seen==PROJECTS and {m for m in external if not is_tool(m)}==set(BOUNDARIES),'Different exact project/external closure.')
 probes=[PREFIX+n for n in NAMES];req(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==probes and len(re.findall(r'^example\b',A.read_text(),re.M))==18,'Different focused audit contract.')
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(g['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing complete supplied Foundation namespace.')
 parent_providers={q['module']:q for q in g['providers']}
 for q in f['providers']:
  if q['module']in parent_providers:req((q['source_sha256'],q['object_sha256'])==(parent_providers[q['module']]['source_sha256'],parent_providers[q['module']]['object_sha256']),'Conflicting exact external boundary '+q['module'])
  parent_providers[q['module']]=q
 providers=[]
 for m,pair in {**BOUNDARIES,**ANCHORS}.items():
  if m!=D1:req((parent_providers[m]['source_sha256'],parent_providers[m]['object_sha256'])==pair,'Wrong historical boundary/anchor pair '+m)
  ss=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path'])/rel(m,'.lean');o=next((x/rel(m,'.olean')for x in [namespace.parent,*libs]if(x/rel(m,'.olean')).is_file()),None)
  req(o is not None and(sha(ss),sha(o))==pair,'Changed actual direct boundary/anchor '+m)
  scope=('Newly direct existing cached Foundation D1 boundary; source read, no prior separate guarded boundary or whole-cache attestation claimed.'if m==D1 else'Exact previously recorded direct external boundary.'if m in BOUNDARIES else'Inherited dependency discovery anchor, not a direct project import.')
  providers.append(dict(module=m,source=str(ss.resolve()),source_sha256=pair[0],object=str(o.resolve()),object_sha256=pair[1],scope=scope,prior_boundary_attestation=m!=D1))
 W.mkdir(parents=True);cache=W/'cache';cache.mkdir();(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 for q in selected.values():
  dest=cache/rel(q['module'],'.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
 obj=cache/rel(MODULE,'.olean');obj.parent.mkdir(parents=True,exist_ok=True);snaps=W/'sources';ss=snaps/rel(MODULE,'.lean');ss.parent.mkdir(parents=True,exist_ok=True);aa=snaps/'Audit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 sysroot=C.parent.parent/'lib/lean';search=[cache,*libs,sysroot];tool_direct={m for f in [S,A]+[Path(q['source'])for q in list(selected.values())+providers]for m in H.lean_imports(f.read_text())if is_tool(m)};tools=[]
 for m in sorted(tool_direct|{'Init','Lean.Elab.Tactic.Omega'}):
  req(m in TOOLS,'Unreviewed toolchain boundary '+m);ref=sysroot/rel(m,'.olean');o=next((x/rel(m,'.olean')for x in search if(x/rel(m,'.olean')).is_file()),None)
  req(o is not None and ref.is_file()and sha(o)==sha(ref)==TOOLS[m],'Wrong actual first/canonical toolchain provider '+m)
  tools.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),actual_first=str(o),toolchain_reference=str(ref),toolchain_reference_sha256=sha(ref)))
 actual=[]
 for q in list(selected.values())+providers:
  o=next((x/rel(q['module'],'.olean')for x in search if(x/rel(q['module'],'.olean')).is_file()),None);req(o is not None and o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Wrong actual first provider '+q['module']);actual.append(dict(module=q['module'],actual_first=str(o),resolved=str(o.resolve()),sha256=sha(o)))
 inputs=[Path(__file__).resolve(),helper,E,G,F,C,D/'lake-manifest.json',S,A,ss,aa]+[Path(q[k])for q in list(selected.values())+providers for k in ['source','object']]+[Path(q[k])for q in tools for k in ['object','toolchain_reference']]
 inputs=list(dict.fromkeys(x.resolve()for x in inputs));before={str(x):sha(x)for x in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Model-independent domL, external relF with exact internal quote bridge, ordinary finite L-axiom proofs and all-internal finite-class discharge. The refutation transport remains conditional on arbitrary internal Separation/Replacement proofs hSchema; no unconditional ConZF/ConZFC or final PA equivalence.',compiler=dict(path=str(C),sha256=sha(C),version=version),compiler_version_query_performed=not a.prepare_only,source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),source_overridden=a.source is not None,audit_overridden=a.audit is not None,provider_evidence=[dict(role='native169',path=str(E),sha256=sha(E),scope='Only selected constructible/native ancestors reused.'),dict(role='actual G',path=str(G),sha256=sha(G),scope='Only selected NativeZF, Delta1 ancestors and exact external provider identities reused; G itself and Cantor are not imported.'),dict(role='fresh827+Set50',path=str(F),sha256=sha(F),scope='Both exact fresh relativization objects imported; no historical701 variant.')],reused_modules=list(selected.values()),providers=providers,direct_external_boundaries=sorted(BOUNDARIES),discovery_anchor_modules=sorted(ANCHORS),toolchain_providers=tools,actual_direct_tool_imports=sorted(tool_direct),actual_first_providers=actual,exact_project_import_closure=True,exact_project_prerequisite_count=36,namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace),whole_namespace_independently_attested=False),dependencies=deps,before=before,commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_mebibytes=4096,per_command_timeout_seconds=a.timeout_seconds,global_option_overrides=[],dependency_build=False,downloads=False,whole_dependency_cache_attested=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
 def post():
  r['after']={str(x):sha(x)for x in inputs};req(before==r['after'],'Changed input during check.')
  for q in list(selected.values())+providers+tools:
   o=next((x/rel(q['module'],'.olean')for x in search if(x/rel(q['module'],'.olean')).is_file()),None);req(o is not None and o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed actual first provider '+q['module'])
  for q in r['fresh_modules']:
   o=next((x/rel(q['module'],'.olean')for x in search if(x/rel(q['module'],'.olean')).is_file()),None);req(o is not None and o.resolve()==Path(q['path']).resolve()and sha(o)==q['sha256'],'Changed fresh/first provider '+q['module'])
  _,dd=H.dependency_libraries(D,a.library_path);req(dd==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 def run(label,file,object_path=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(object_path)]if object_path else[])+[str(file)];t=time.monotonic()
  try:cp=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True,timeout=a.timeout_seconds);out=cp.stdout+cp.stderr;code=cp.returncode;timedout=False
  except subprocess.TimeoutExpired as ex:
   def txt(x):return x.decode(errors='replace')if isinstance(x,bytes)else(x or'')
   out=txt(ex.stdout)+txt(ex.stderr);code=None;timedout=True
  (W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=code,timed_out=timedout,output=out));save();req(not timedout,'Compiler timeout; retained FAIL.');req(code==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 save()
 try:
  if a.prepare_only:post();save();print(W/'verification.json');return
  run('source',ss,obj);fresh=dict(module=MODULE,path=str(obj),sha256=sha(obj),source_sha256=sha(S));r['fresh_modules'].append(fresh);save();out=run('audit',aa)
  reports=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.M);req([n for n,_ in reports]==probes and all({x.strip()for x in ax.split(',')if x.strip()}<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong ordered standard theorem reports.')
  req(sha(obj)==fresh['sha256'],'Fresh object changed through audit.');post();r.update(status='PASS',named_axiom_probes=25,callers=18,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException as ex:r.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
