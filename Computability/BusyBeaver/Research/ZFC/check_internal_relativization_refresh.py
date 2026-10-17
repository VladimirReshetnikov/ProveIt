"""Fresh consolidated represented relativization and the function-free set adapter.
Sequential source/audit checks only. Prepare-only invokes no Lean binary/version query.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,sys,time
sys.dont_write_bytecode=True
BASE='BoundedPAConsistency.InternalRelativization'
SET='ZFCinPA.SetRelativization'
INSTANCE='ZFCinPA.Instances'
BASE_SHA='a64c5e65dd235068fb1d62d8e82be55a6f325375d081663fa8dc2a946e2ad11a'
SET_SHA='b2d4cec4106aa5ff68a66b1b624415b4ec91f8bcb542340716b83d1f3eadfdae'
BASE_AUDIT_SHA='ad6e038b6fc26291f3acc8827139db122fd300511d00cc0ae98f2a6278d9b4aa'
SET_AUDIT_SHA='ab4d0a8fffc411aa742ec48d37cfd92a7a622e01a6e54d9b9acaa6edc5951710'
INSTANCE_PAIR=('30965b8b9533ae07fcfddf7743cd247df1ebd6a1224d4d4982786aa5bfe2446d','50532105d60be5b437537109a6ca8e37b2d883659dc4a64774fe5bf93d81595c')
HELPER_SHA='9a8d4d7dd467ac8152238c8a0cbe93ed87512be36b447e38bae0b8244a28b229'
BASIC_RECORDS={'1f9d7d719ed52af373162b432a63df4a30c026e8690c56c98b614609feb8663c','c69bf7789ef2dfa3162bcf27d791312bbb76942636408ef4cd377a885d073d35'}
SET_RECORD='2a235367a454a23c709bce36e924c11d7a23e55394d7aef6eb314b17143dfc4e'
BASIC='Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic'
AXIOMS='Foundation.FirstOrder.SetTheory.Basic.Axioms'
SYNTAX='Foundation.FirstOrder.Bootstrapping.Syntax'
BOUNDARIES={
 BASIC:('72e3cf386967e3fed4366ee5aa59678a0333cd2f40c8dbb09bebbf8dd4fa80e3','c46f491eded2b033f450406537c1e02b6135a6b563f18a6cac1589f535ad5b69'),
 'Foundation.FirstOrder.Arithmetic.IOpen.Basic':('4ec52a7a487aeafb0e9ea10716452b34f138d8214ad5a1aa5466064d6a4c9d7b','b43eb2f8d8a2ef18004125594adafbff02b52f1b6ef62b9b836015bdce2351ad'),
 'Mathlib.Tactic.Ring':('d3ef5c49ebbd1108ce3f935e5ad95485e143abf02f28c027dba4bb6f3be8196e','cc12dfa66db7ef6ae4cd2d7a4e035ddffaca827168243f728812776b77836eb4'),
 AXIOMS:('9952df1012c4eeb08eb2f40b1719a1912856ce013daec5735a9ac81a97f4c9b8','e2654fef89ea6d605dbb52b87ad19d2b9e98ed3c532f6d3145689d404d5f0704'),
 SYNTAX:('18257680a6f1d84b6b4ae3d6dc5c07f4adcd4aa660fe3d4f63fa4df98932c79c','7eecf0d4bf8fd67fd59dba66deb007a78da940367d3e3b932f5a6f19eb14a23c')}
TOOLS={'Init':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e','Lean':'1c099f2b3587535ed451498b40390f140751d66760f5831dfe92ecd198968e74','Std':'47c15fd871e3e77f25ed908e07c0914aa52b8abec810c728e2a152598e7f7644','Lean.Elab.Tactic.Omega':'eb766bae1ab40110a853c7cca853e36e1f4aece010a09fa4dd9b1b48116953fe'}
BASE_NAMES=['isUFormula_relativize','isSemiformula_relativize','relativize_neg','relativize_shift','subst_eq_self_of_prefix','subst_qVec_domain','relativize_subst','relativize_substs1','relativize_free','setShift_relSet','derivable_relSet','domSet_succ','derivable_of_domSet_succ','derivable_of_domSet','provable_relativize','provable_falsum_of_relativize']
SET_NAMES=['set_not_isFunc','isTerm_eq_fvar','provable_falsum_of_relativize_set']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise RuntimeError(msg)
def rel(m,suffix):return Path(m.replace('.','/')).with_suffix(suffix)
def main():
 p=argparse.ArgumentParser(description=__doc__)
 for k in ['repo','dependency-root','output']:p.add_argument('--'+k,type=Path,required=True)
 for k in ['base-source','set-source','base-audit','set-audit','provider-evidence','set-provider-evidence','instances-cache','namespace-cache','lean']:p.add_argument('--'+k,type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[])
 p.add_argument('--prepare-only',action='store_true');p.add_argument('--timeout-seconds',type=int,default=120);a=p.parse_args()
 if not __debug__:p.error('Python -O is unsupported: identity guards must remain enabled.')
 req(1<=a.timeout_seconds<=300,'Timeout must be between1 and300 seconds.')
 R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve();PA=R/'Logic/PeanoArithmetic/BoundedConsistency/Lean';Z=R/'Logic/Interpretability/ZFCinPA'
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or(W.is_dir()and not any(W.iterdir()))),'Fresh external output required.')
 S1=(a.base_source or PA/rel(BASE,'.lean')).resolve();S2=(a.set_source or Z/'Lean'/rel(SET,'.lean')).resolve()
 A1=(a.base_audit or PA/'BoundedPAConsistency/InternalRelativizationFullAudit.lean').resolve();A2=(a.set_audit or Z/'Lean/ZFCinPA/SetRelativizationRefreshAudit.lean').resolve()
 req((sha(S1),sha(S2),sha(A1),sha(A2))==(BASE_SHA,SET_SHA,BASE_AUDIT_SHA,SET_AUDIT_SHA),'Changed frozen source/audit.')
 E=(a.provider_evidence or R/'Computability/BusyBeaver/Research/ZFC/results/internal-axiom-proof-transport-verification.json').resolve()
 G=(a.set_provider_evidence or Z/'results/model-coded-decoder-collection254-verification.json').resolve()
 req(sha(E)in BASIC_RECORDS and sha(G)==SET_RECORD,'Wrong exact existing provider evidence.')
 e=json.loads(E.read_text());g=json.loads(G.read_text())
 for q,counts in [(e,(3,7)),(g,(10,16))]:
  req(q['status']=='PASS'and(q['named_axiom_probes'],q['callers'])==counts and q['only_standard_axioms']and q['all_input_provider_postchecks']and q['all_fresh_objects_unchanged_after_audit'],'Wrong provider-evidence PASS contract.')
 req((e['source']['sha256'],e['audit']['sha256'])==('8efca1f6d357ee37b6cb0a08d684b48bf41ceae775b67182942de1b26ec473ad','326e0bd28075df6ec2d3273355e691b48cff6a67fad9ceac6298dde01146fd7f'),'Wrong historical Basic provider source/audit.')
 req((g['source']['sha256'],g['audit']['sha256'])==('64a133445dde69c2e642ab6397c2b72c51bd025f2843412a9d5bc8a8c2eeaa3e','a9798acde4a76cdf640fbb3bed348c5824dfbc5fe87c51eef24ab2605d117544'),'Wrong historical set-provider source/audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';req(sha(helper)==HELPER_SHA,'Changed discovery helper.')
 sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C=(a.lean or Path(e['compiler']['path'])).expanduser().resolve();req(sha(C)==e['compiler']['sha256']==g['compiler']['sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','Wrong pinned compiler binary.')
 version=e['compiler']['version'];req(version==g['compiler']['version']and version.startswith('Lean (version 4.32.0,'),'Different recorded compiler.')
 if not a.prepare_only:req(subprocess.check_output([str(C),'--version'],text=True).strip()==version,'Different observed compiler version.')
 libs,deps=H.dependency_libraries(D,a.library_path)
 for record in [e,g]:
  for n in ['Foundation','Mathlib']:req(deps[n]['pin']==record['dependencies'][n]['pin']and deps[n]['tracked_clean']and record['dependencies'][n]['tracked_clean'],'Different dependency pin/tracked state.')
  req(deps['lake_manifest_sha256']==record['dependencies']['lake_manifest_sha256'],'Different dependency manifest.')
  for m,q in deps['providers'].items():req(q['sha256']==record['dependencies']['providers'][m]['sha256'],'Different discovery anchor '+m)
 parent_basic={q['module']:q for q in e['providers']};parent_set={q['module']:q for q in g['providers']}
 req(set(parent_basic)=={BASIC,'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring'},'Wrong Basic-provider boundary set.')
 parent_instances=[q for q in g['reused_modules']if q['module']==INSTANCE];req(len(parent_instances)==1,'Missing unique checked Instances prerequisite.');old=parent_instances[0]
 req((old['source_sha256'],old['object_sha256'])==INSTANCE_PAIR,'Wrong checked Instances pair.')
 IS=Z/'Lean'/rel(INSTANCE,'.lean');IO=(a.instances_cache/rel(INSTANCE,'.olean')if a.instances_cache else Path(old['object'])).resolve()
 req((sha(IS),sha(IO))==INSTANCE_PAIR,'Changed Instances source/object.')
 reused=[dict(module=INSTANCE,source=str(IS),source_sha256=sha(IS),object=str(IO),object_sha256=sha(IO))]
 namespace=(a.namespace_cache/'Foundation'if a.namespace_cache else Path(g['namespace_overlay']['target'])).resolve();req(namespace.is_dir(),'Missing complete supplied Foundation namespace.')
 providers=[]
 for m,pair in BOUNDARIES.items():
  old=(parent_basic if m in parent_basic else parent_set)[m];req((old['source_sha256'],old['object_sha256'])==pair,'Wrong historical boundary pair '+m)
  ss=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path'])/rel(m,'.lean');o=next((x/rel(m,'.olean')for x in [namespace.parent,*libs]if(x/rel(m,'.olean')).is_file()),None)
  req(o is not None and(sha(ss),sha(o))==pair,'Changed selected boundary '+m)
  providers.append(dict(module=m,source=str(ss.resolve()),source_sha256=pair[0],object=str(o.resolve()),object_sha256=pair[1],scope='Actual direct external boundary'if m in {BASIC,AXIOMS,SYNTAX}else'Inherited dependency discovery anchor; no direct project import.'))
 req(H.lean_imports(S1.read_text())==[BASIC]and H.lean_imports(S2.read_text())==[INSTANCE,BASE]and H.lean_imports(IS.read_text())==[AXIOMS,SYNTAX],'Wrong exact source import closure.')
 scopes=[]
 for module,S,A,short,names,callers,prefix in [(BASE,S1,A1,'base',BASE_NAMES,18,'LeanProofs.BoundedPAConsistency.InternalRelativization.'),(SET,S2,A2,'set',SET_NAMES,6,'LeanProofs.ZFCinPA.SetRelativization.')]:
  probes=[prefix+n for n in names];req(H.lean_imports(A.read_text())==[module]and re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==probes and len(re.findall(r'^example\b',A.read_text(),re.M))==callers,'Wrong ordered focused audit '+short)
  scopes.append(dict(module=module,source=str(S),source_sha256=sha(S),audit=str(A),audit_sha256=sha(A),label=short,probes=probes,callers=callers))
 W.mkdir(parents=True);cache=W/'cache';cache.mkdir();(cache/'Foundation').symlink_to(namespace,target_is_directory=True)
 dest=cache/rel(INSTANCE,'.olean');dest.parent.mkdir(parents=True);dest.symlink_to(IO);(cache/'BoundedPAConsistency').mkdir()
 snaps=W/'sources'
 for q in scopes:
  ss=snaps/rel(q['module'],'.lean');ss.parent.mkdir(parents=True,exist_ok=True);aa=snaps/(q['label']+'Audit.lean');shutil.copyfile(q['source'],ss);shutil.copyfile(q['audit'],aa);q.update(snapshot=str(ss),audit_snapshot=str(aa))
 sysroot=C.parent.parent/'lib/lean';search=[cache,*libs,sysroot];direct_tools={m for f in [S1,S2,A1,A2,IS]+[Path(q['source'])for q in providers]for m in H.lean_imports(f.read_text())if m in {'Init','Std','Lean'}or m.startswith(('Lean.','Std.'))};tools=[]
 for m in sorted(direct_tools|{'Init','Lean.Elab.Tactic.Omega'}):
  req(m in TOOLS,'Unreviewed toolchain boundary '+m);ref=sysroot/rel(m,'.olean');o=next((x/rel(m,'.olean')for x in search if(x/rel(m,'.olean')).is_file()),None)
  req(o is not None and ref.is_file()and sha(o)==sha(ref)==TOOLS[m],'Wrong actual/canonical toolchain provider '+m)
  tools.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(ref),toolchain_reference_sha256=sha(ref)))
 inputs=[Path(__file__).resolve(),helper,E,G,C,D/'lake-manifest.json']+[Path(q[k])for q in scopes for k in ['source','audit','snapshot','audit_snapshot']]+[Path(q[k])for q in reused+providers for k in ['source','object']]+[Path(q[k])for q in tools for k in ['object','toolchain_reference']]
 inputs=list(dict.fromkeys(x.resolve()for x in inputs));before={str(x):sha(x)for x in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Fresh consolidated827 represented relativization with conditional side discharge, then unchanged50-line set-language term premise adapter. Actual domain/nonemptiness/translated axioms, L interpretation and PA equivalence remain obligations.',sources=scopes,provider_evidence=[dict(role='Basic',path=str(E),sha256=sha(E)),dict(role='Instances and set boundaries',path=str(G),sha256=sha(G))],compiler=dict(path=str(C),sha256=sha(C),version=version),compiler_version_query_performed=not a.prepare_only,reused_modules=reused,providers=providers,toolchain_providers=tools,actual_direct_tool_imports=sorted(direct_tools),direct_external_boundaries=[BASIC,AXIOMS,SYNTAX],discovery_anchor_modules=sorted(deps['providers']),exact_project_prerequisite_count=1,exact_project_import_closure=[BASE,SET,INSTANCE],namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace),whole_namespace_independently_attested=False),dependencies=deps,before=before,commands=[],fresh_modules=[],audit_results=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_mebibytes=4096,per_command_timeout_seconds=a.timeout_seconds,source_overrides=dict(base=a.base_source is not None,set=a.set_source is not None),audit_overrides=dict(base=a.base_audit is not None,set=a.set_audit is not None),global_option_overrides=[],dependency_build=False,downloads=False,whole_dependency_cache_attested=False)
 def save():(W/'verification.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
 def post():
  r['after']={str(x):sha(x)for x in inputs};req(before==r['after'],'Changed input during check.')
  for q in reused+providers+tools:
   o=next((x/rel(q['module'],'.olean')for x in search if(x/rel(q['module'],'.olean')).is_file()),None)
   req(o is not None and o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed actual first provider '+q['module'])
  for q in r['fresh_modules']:
   o=next((x/rel(q['module'],'.olean')for x in search if(x/rel(q['module'],'.olean')).is_file()),None)
   req(o is not None and o.resolve()==Path(q['path']).resolve()and sha(o)==q['sha256'],'Changed fresh/first provider '+q['module'])
  _,dd=H.dependency_libraries(D,a.library_path);req(dd==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 def run(label,file,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic()
  try:cp=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True,timeout=a.timeout_seconds);out=cp.stdout+cp.stderr;code=cp.returncode;timedout=False
  except subprocess.TimeoutExpired as ex:
   def text(x):return x.decode(errors='replace')if isinstance(x,bytes)else(x or'')
   out=text(ex.stdout)+text(ex.stderr);code=None;timedout=True
  (W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=code,timed_out=timedout,output=out));save();req(not timedout,'Compiler timeout; retained FAIL.');req(code==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out);print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 save()
 try:
  if a.prepare_only:post();save();print(W/'verification.json');return
  for q in scopes:
   obj=cache/rel(q['module'],'.olean');run(q['label']+'-source',Path(q['snapshot']),obj);fresh=dict(module=q['module'],path=str(obj),sha256=sha(obj),source_sha256=q['source_sha256']);r['fresh_modules'].append(fresh);save()
   out=run(q['label']+'-audit',Path(q['audit_snapshot']));reports=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.M)
   req([n for n,_ in reports]==q['probes']and all({x.strip()for x in ax.split(',')if x.strip()}<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong ordered theorem reports '+q['label'])
   req(sha(obj)==fresh['sha256'],'Fresh object changed through audit.');r['audit_results'].append(dict(module=q['module'],named_axiom_probes=len(q['probes']),callers=q['callers'],only_standard_axioms=True));save()
  post();r.update(status='PASS',named_axiom_probes=19,callers=24,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
 except BaseException as ex:r.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
