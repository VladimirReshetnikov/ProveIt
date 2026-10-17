"""Fresh full represented relativization source plus extended formation/transport audit.
Prepare-only invokes no Lean binary or --version. No dependency builds/downloads.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,os,re,shutil,subprocess,sys,time
sys.dont_write_bytecode=True
MODULE='BoundedPAConsistency.InternalRelativization'
SOURCE_SHA='6f5a20fa167d810a5c6cbbab001f33f217737de1b97d5e9ab55cf6612856c440'
AUDIT_SHA='31db0225aa9af67ef271332bd572f11203937741aadc27572b0211aeb1fabc92'
HELPER_SHA='9a8d4d7dd467ac8152238c8a0cbe93ed87512be36b447e38bae0b8244a28b229'
PARENT_HASHES={'1f9d7d719ed52af373162b432a63df4a30c026e8690c56c98b614609feb8663c','c69bf7789ef2dfa3162bcf27d791312bbb76942636408ef4cd377a885d073d35'}
BASIC='Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic'
NAMES=['isUFormula_relativize','isSemiformula_relativize','relativize_neg','relativize_shift','subst_eq_self_of_prefix','subst_qVec_domain','relativize_subst','relativize_substs1','relativize_free','setShift_relSet','derivable_relSet']
PROBES=['LeanProofs.BoundedPAConsistency.InternalRelativization.'+n for n in NAMES]
BOUNDARIES={
 BASIC:('72e3cf386967e3fed4366ee5aa59678a0333cd2f40c8dbb09bebbf8dd4fa80e3','c46f491eded2b033f450406537c1e02b6135a6b563f18a6cac1589f535ad5b69'),
 'Foundation.FirstOrder.Arithmetic.IOpen.Basic':('4ec52a7a487aeafb0e9ea10716452b34f138d8214ad5a1aa5466064d6a4c9d7b','b43eb2f8d8a2ef18004125594adafbff02b52f1b6ef62b9b836015bdce2351ad'),
 'Mathlib.Tactic.Ring':('d3ef5c49ebbd1108ce3f935e5ad95485e143abf02f28c027dba4bb6f3be8196e','cc12dfa66db7ef6ae4cd2d7a4e035ddffaca827168243f728812776b77836eb4')}
TOOLS={'Init':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e','Lean':'1c099f2b3587535ed451498b40390f140751d66760f5831dfe92ecd198968e74','Std':'47c15fd871e3e77f25ed908e07c0914aa52b8abec810c728e2a152598e7f7644','Lean.Elab.Tactic.Omega':'eb766bae1ab40110a853c7cca853e36e1f4aece010a09fa4dd9b1b48116953fe'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def req(ok,msg):
 if not ok:raise RuntimeError(msg)
def rel(m,suffix):return Path(m.replace('.','/')).with_suffix(suffix)
def main():
 p=argparse.ArgumentParser(description=__doc__)
 for key in ['repo','dependency-root','output']:p.add_argument('--'+key,type=Path,required=True)
 for key in ['source','audit','provider-evidence','lean']:p.add_argument('--'+key,type=Path)
 p.add_argument('--library-path',type=Path,action='append',default=[])
 p.add_argument('--prepare-only',action='store_true');p.add_argument('--timeout-seconds',type=int,default=120)
 a=p.parse_args()
 if not __debug__:p.error('Python -O is unsupported: all identity guards must remain enabled.')
 req(1<=a.timeout_seconds<=300,'Timeout must be between1 and300 seconds.')
 R=a.repo.resolve();D=a.dependency_root.resolve();W=a.output.resolve()
 req(not W.is_relative_to(R)and not W.is_relative_to(D)and(not W.exists()or(W.is_dir()and not any(W.iterdir()))),'Fresh external output required.')
 S=(a.source or R/'Logic/PeanoArithmetic/BoundedConsistency/Lean'/rel(MODULE,'.lean')).resolve()
 A=(a.audit or R/'Logic/PeanoArithmetic/BoundedConsistency/Lean/BoundedPAConsistency/InternalRelativizationExtendedAudit.lean').resolve()
 E=(a.provider_evidence or R/'Computability/BusyBeaver/Research/ZFC/results/internal-axiom-proof-transport-verification.json').resolve()
 req(sha(S)==SOURCE_SHA and sha(A)==AUDIT_SHA,'Wrong frozen source/audit; obtain review before changing pins.')
 req(sha(E)in PARENT_HASHES,'Wrong exact existing Basic-provider evidence.')
 e=json.loads(E.read_text());req(e['status']=='PASS'and e['named_axiom_probes']==3 and e['callers']==7 and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Wrong provider-evidence PASS contract.')
 req(e['source']['sha256']=='8efca1f6d357ee37b6cb0a08d684b48bf41ceae775b67182942de1b26ec473ad'and e['audit']['sha256']=='326e0bd28075df6ec2d3273355e691b48cff6a67fad9ceac6298dde01146fd7f','Wrong historical proof-transport source/audit.')
 helper=R/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py';req(sha(helper)==HELPER_SHA,'Changed dependency discovery helper.')
 sp=importlib.util.spec_from_file_location('H',helper);H=importlib.util.module_from_spec(sp);sp.loader.exec_module(H)
 C=(a.lean or Path(e['compiler']['path'])).expanduser().resolve();req(sha(C)==e['compiler']['sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','Wrong pinned compiler binary.')
 version=e['compiler']['version'];req(version.startswith('Lean (version 4.32.0,'),'Wrong recorded compiler version.')
 if not a.prepare_only:req(subprocess.check_output([str(C),'--version'],text=True).strip()==version,'Different observed compiler version.')
 libs,deps=H.dependency_libraries(D,a.library_path)
 for name in ['Foundation','Mathlib']:
  req(deps[name]['pin']==e['dependencies'][name]['pin']and deps[name]['tracked_clean']and e['dependencies'][name]['tracked_clean'],'Different dependency pin/tracked state.')
 req(deps['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256'],'Different dependency manifest.')
 for m,q in deps['providers'].items():req(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Different discovery anchor '+m)
 req(H.lean_imports(S.read_text())==[BASIC]and H.lean_imports(A.read_text())==[MODULE],'Wrong direct source/audit imports.')
 req(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==PROBES and len(re.findall(r'^example\b',A.read_text(),re.M))==12,'Wrong ordered11-probe/12-caller audit.')
 parent_providers={q['module']:q for q in e['providers']};req(set(parent_providers)==set(BOUNDARIES),'Wrong exact existing provider set.')
 providers=[]
 for m,(sh,oh)in BOUNDARIES.items():
  old=parent_providers[m];req((old['source_sha256'],old['object_sha256'])==(sh,oh),'Wrong historical source/object pair '+m)
  ss=Path(deps['Foundation'if m.startswith('Foundation.')else'Mathlib']['path'])/rel(m,'.lean')
  o=next((x/rel(m,'.olean')for x in libs if(x/rel(m,'.olean')).is_file()),None)
  req(o is not None and sha(ss)==sh and sha(o)==oh,'Changed actual selected boundary '+m)
  providers.append(dict(module=m,source=str(ss.resolve()),source_sha256=sh,object=str(o.resolve()),object_sha256=oh,scope='Actual direct source/object boundary'if m==BASIC else'Inherited dependency-discovery anchor; not a direct client import.'))
 W.mkdir(parents=True,exist_ok=True);cache=W/'cache';(cache/'BoundedPAConsistency').mkdir(parents=True);snaps=W/'sources';ss=snaps/rel(MODULE,'.lean');ss.parent.mkdir(parents=True);aa=snaps/'ExtendedAudit.lean';shutil.copyfile(S,ss);shutil.copyfile(A,aa)
 sysroot=C.parent.parent/'lib/lean';search=[cache,*libs,sysroot]
 direct_tools={m for f in [S,A]+[Path(q['source'])for q in providers]for m in H.lean_imports(f.read_text())if m in {'Init','Lean','Std'}or m.startswith(('Lean.','Std.'))}
 tools=[]
 for m in sorted(direct_tools|{'Init','Lean.Elab.Tactic.Omega'}):
  req(m in TOOLS,'New toolchain boundary requires explicit review '+m)
  ref=sysroot/rel(m,'.olean');o=next((x/rel(m,'.olean')for x in search if(x/rel(m,'.olean')).is_file()),None)
  req(o is not None and ref.is_file()and sha(o)==sha(ref)==TOOLS[m],'Wrong actual/canonical toolchain provider '+m)
  tools.append(dict(module=m,object=str(o.resolve()),object_sha256=sha(o),toolchain_reference=str(ref),toolchain_reference_sha256=sha(ref)))
 inputs=[Path(__file__).resolve(),helper,E,C,S,A,ss,aa,D/'lake-manifest.json']+[Path(q[k])for q in providers for k in ['source','object']]+[Path(q[k])for q in tools for k in ['object','toolchain_reference']]
 inputs=list(dict.fromkeys(x.resolve()for x in inputs));before={str(x):sha(x)for x in inputs}
 env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
 r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',scope='Fresh full represented relativization: total syntax/formula laws and conditional all-internal derivation transport with finite domain side formulas. No side-formula discharge, actual L axiom proof, C254 reverse adapter or final PA equivalence.',source=dict(path=str(S),sha256=sha(S),snapshot=str(ss)),audit=dict(path=str(A),sha256=sha(A),snapshot=str(aa)),provider_evidence=dict(path=str(E),sha256=sha(E)),compiler=dict(path=str(C),sha256=sha(C),version=version),compiler_version_query_performed=not a.prepare_only,providers=providers,toolchain_providers=tools,actual_direct_tool_imports=sorted(direct_tools),direct_external_boundaries=[BASIC],discovery_anchor_modules=sorted(deps['providers']),dependencies=deps,reused_project_modules=[],exact_project_prerequisite_count=0,fresh_modules=[],before=before,commands=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_mebibytes=4096,per_command_timeout_seconds=a.timeout_seconds,source_overridden=a.source is not None,audit_overridden=a.audit is not None,global_option_overrides=[],dependency_build=False,downloads=False,whole_dependency_cache_attested=False)
 def save():(W/'verification.json').write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')
 def post():
  r['after']={str(x):sha(x)for x in inputs};req(before==r['after'],'Changed input during check.')
  for q in providers+tools:
   o=next((x/rel(q['module'],'.olean')for x in search if(x/rel(q['module'],'.olean')).is_file()),None)
   req(o is not None and o.resolve()==Path(q['object']).resolve()and sha(o)==q['object_sha256'],'Changed actual first provider '+q['module'])
  _,newdeps=H.dependency_libraries(D,a.library_path);req(newdeps==deps,'Changed dependency state.');r['all_input_provider_postchecks']=True
 def run(label,file,obj=None):
  cmd=[str(C),'-M4096','--root='+str(snaps)]+(['-o',str(obj)]if obj else[])+[str(file)];t=time.monotonic()
  try:
   cp=subprocess.run(cmd,cwd=snaps,env=env,text=True,capture_output=True,timeout=a.timeout_seconds);out=cp.stdout+cp.stderr;code=cp.returncode;timedout=False
  except subprocess.TimeoutExpired as ex:
   def text(x):return x.decode(errors='replace')if isinstance(x,bytes)else(x or'')
   out=text(ex.stdout)+text(ex.stderr);code=None;timedout=True
  (W/(label+'.log')).write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-t,exit_code=code,timed_out=timedout,output=out));save()
  req(not timedout,'Compiler timeout; preserved as FAIL.');req(code==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,out)
  print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
 save()
 try:
  if a.prepare_only:post();save();print(W/'verification.json');return
  obj=cache/rel(MODULE,'.olean');run('source',ss,obj);fresh=dict(module=MODULE,path=str(obj),sha256=sha(obj),source_sha256=sha(S));r['fresh_modules'].append(fresh);save()
  out=run('audit',aa)
  reports=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.M)
  req([n for n,_ in reports]==PROBES and all({x.strip()for x in ax.split(',')if x.strip()}<={'propext','Classical.choice','Quot.sound'}for _,ax in reports),'Wrong ordered theorem axiom reports.')
  post();req(sha(obj)==fresh['sha256'],'Fresh object changed through audit.')
  r.update(status='PASS',named_axiom_probes=11,callers=12,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']),axiom_reports=[dict(theorem=n,axioms=[x.strip()for x in ax.split(',')if x.strip()])for n,ax in reports])
 except BaseException as ex:r.update(status='FAIL',error=str(ex));save();raise
 save();print(W/'verification.json')
if __name__=='__main__':main()
