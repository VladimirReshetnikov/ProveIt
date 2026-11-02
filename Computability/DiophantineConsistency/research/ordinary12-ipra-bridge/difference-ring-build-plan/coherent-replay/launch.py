#!/usr/bin/env python3
"""Pinned, fail-closed launcher for the reviewed coexistence-only pair."""
import hashlib,importlib.util,json,os,signal,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
 raise RuntimeError('launcher rejects optimized Python and PYTHONOPTIMIZE')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[5];PLAN=HERE.parent;MON=PLAN/'monitor';REV=ROOT/'Computability/DiophantineConsistency/reviews';FRESH=ROOT/'Computability/DiophantineConsistency/research/fresh-project-closure'
SNAP=Path('/tmp/ipra-ordinary12-coexistence-source-03');PROVIDER=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json');FINPUT=REV/'foundation-provider-recovery/input-manifest.json';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
OUTPUT=Path('/tmp/ipra-ordinary12-coexistence-pair-01');PREFLIGHT=Path('/tmp/ipra-ordinary12-coexistence-preflight-01.json');TERMINAL=Path('/tmp/ipra-ordinary12-coexistence-launch-terminal-01.json')
SNAP_SHA='9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded';PROVIDER_SHA='7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6';FINPUT_SHA='491075df9eac57799d21b475527b3b1af3dc81ded58e97a87e1cf6c453dcb13d';LEAN_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
PINS={HERE/'gates.py':'76f153b8be70b4c804469934c2dcaf92f9803f0024932a48674c96d3b47d373e',HERE/'REAL-RUN.md':'d60575b7a89aae56976710d076f87285261066ee1fa5f432250cdd7b33274f08',MON/'paired.py':'b3eb4021ae3d8797adcb796bcbe3613a9363ea5b4917d85173e92e27c08f9910',MON/'monitor.py':'f83085ddc84b9376d934cfbc4b29cd28b91f10a7f1ac28fd372e276b5cf542ee',MON/'path_guard.py':'9af0852abe419dee3fa83a57aa8fbdb3584285c8c40a229c9ef041f610375173',FRESH/'rebuild.py':'8170bd401b1821666fffc2a55f8dd908e473d32c71797661a5acd85a32d0dc56',FRESH/'compare.py':'530def48c58dc38ce8a293a5c9912762b2ad101e63faf7cb0763f71a7ac9a3a5'}
REVIEWS=[
 ('ordinary12-isolated-chain-independent-audit','CHECK.json','1fb0d748f9c2c216d6ed00a7414d297124d5ea3aed28a02ed1bf46ce8616492d','9299eb27ac06463975b9b71f2a61e934ce4bc8828c8065b4c3c2b4253e84786c','PASS_TOY_ISOLATED_WRAPPER_CHAIN','audit_observed_exit_code','receipt_sha256'),
 ('ordinary12-coherent-runbook-independent-audit','receipt.json','13bb273e561e1cc6f80ec0fa6aebaed4ee7ece5580ab5a2858f037c745d814ca','2456472477aca04d8259e4f0f76897944502028ab25c19aa90f6a45b74dc77f1','PASS_INDEPENDENT_COHERENT_RUNBOOK_STATIC_AUDIT','audit_observed_exit_code','receipt_sha256'),
 ('ordinary12-coherent-source03-independent-audit','receipt.json','4e93e1ed0a30af3c1dd0fb8b1101fa1cf6d571243659042f50114abf5e500242','4f22608282c9928378a15cc82fc0a0bee17aec99295bd27a07e7e820495cbe82','PASS_INDEPENDENT_COHERENT_SOURCE03_AUDIT','audit_observed_exit_code','receipt_sha256'),
 ('ordinary12-sampled-monitor-independent-audit','corrected-receipt.json','98ea151f82dc8e34b71eed019d3932c9bf653829d0f1ce19cbcfa13233e9b295','be1d904dc71b565d95c5232618b3ed2c0c08ba8122baba4b085613e414656762','PASS_INDEPENDENT_CORRECTED_MONITOR_CONTROLS','corrected_review_exit_code','corrected_review_receipt_sha256'),
 ('ordinary12-coherent-freezer-independent-audit','corrected-receipt.json','879c0b90c2db9e8bff19da19486f3a6e90e5e0d55c79fcc220dc7e4feb12175d','59e3d81dfd37f8d0064330590ff2a05e7b4dcdb02c1af942636525bebf931c68','PASS_INDEPENDENT_CORRECTED_FREEZER_CONTROLS','corrected_review_exit_code','corrected_receipt_sha256'),
 ('foundation-provider-independent-audit','receipt.json','60b8bcf556c275a33cbd133f1729fef439a2eaf4c3377d53e4ddbcafb9632a9e','a16d1f6f9b6bf45ecc23d4137c858c0945e3dfb96c1a9dad6fa69d9091dde14d','PASS_PROVIDER_POINT_IN_TIME_AUDIT_OUTER_EXIT_UNOBSERVED','observed_exit_code','receipt_sha256'),
]
def raw_sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load_pinned(name,path,expected):
 if raw_sha(path)!=expected:raise ValueError(('module pin mismatch',name))
 spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def child_environment():
 env=os.environ.copy()
 for name in tuple(env):
  if name.startswith('PYTHON') or name in ('LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
   env.pop(name,None)
 # The coordinator and its Python children use only the reviewed stdlib-based
 # scripts; do not admit user-site startup hooks.
 env['PYTHONNOUSERSITE']='1'
 return env

def require_isolated_startup():
 if not sys.flags.isolated or not sys.flags.no_site:
  raise RuntimeError('invoke launcher as python3 -I -S launch.py')

def preflight():
 for p,h in PINS.items():
  if raw_sha(p)!=h:raise ValueError(('fixed pin drift',str(p)))
 gates=load_pinned('coexistence_gates',HERE/'gates.py',PINS[HERE/'gates.py'])
 guard=load_pinned('coexistence_path_guard',MON/'path_guard.py',PINS[MON/'path_guard.py'])
 reviews=[]
 for folder,file,rsha,tsha,status,exit_key,sha_key in REVIEWS:
  reviews.append(gates.check_review(REV/folder/file,rsha,REV/folder/'terminal-observation.json',tsha,status,exit_key,sha_key))
 protected=[SNAP,PROVIDER.parent,FINPUT,LEAN,ROOT]
 for path in (OUTPUT,PREFLIGHT,TERMINAL):guard.fresh_output(path,protected)
 source=gates.check_sources(SNAP,SNAP_SHA,ROOT,'DiophantineConsistency.FreeJProviderChecks',70)
 provider=gates.check_provider(PROVIDER,PROVIDER_SHA,FINPUT,FINPUT_SHA,LEAN,LEAN_SHA,source['direct_foundation_imports'])
 # Repeat source and all fixed pins after the potentially lengthy provider check.
 source=gates.check_sources(SNAP,SNAP_SHA,ROOT,'DiophantineConsistency.FreeJProviderChecks',70)
 for p,h in PINS.items():
  if raw_sha(p)!=h:raise ValueError(('fixed pin drift after checks',str(p)))
 for folder,file,rsha,tsha,status,exit_key,sha_key in REVIEWS:
  gates.check_review(REV/folder/file,rsha,REV/folder/'terminal-observation.json',tsha,status,exit_key,sha_key)
 for path in (OUTPUT,PREFLIGHT,TERMINAL):guard.fresh_output(path,protected)
 fs=os.statvfs('/tmp');free=fs.f_bavail*fs.f_frsize
 if free<4*1024**3:raise ValueError(('free space below sampled prelaunch threshold',free))
 return {'status':'PASS_PINNED_COEXISTENCE_PREFLIGHT','source':source,'provider':provider,'reviews':reviews,'free_disk_bytes':free,'fixed_sha256':{str(p):h for p,h in PINS.items()},'scope':'Point-in-time preflight only; no hard quota, continuous reserve, Foundation outer-exit observation, Lean project replay, graph transport or iPRA proof.'}

def main():
 if len(sys.argv)!=1:raise ValueError('launcher takes no arguments')
 require_isolated_startup()
 pre=preflight()
 with PREFLIGHT.open('x') as f:json.dump(pre,f,indent=2,sort_keys=True);f.write('\n')
 print('PREFLIGHT_PASS',raw_sha(PREFLIGHT),flush=True)
 # Isolated coordinator startup avoids Python site hooks. In isolated mode
 # Python omits the script directory, so add only this pinned wrapper's parent.
 bootstrap="import runpy,sys; from pathlib import Path; p=Path(sys.argv[1]).resolve(strict=True); sys.path.insert(0,str(p.parent)); sys.argv=sys.argv[1:]; runpy.run_path(str(p),run_name='__main__')"
 cmd=[sys.executable,'-I','-S','-c',bootstrap,str(MON/'paired.py'),'--output',str(OUTPUT),'--snapshot',str(SNAP),'--snapshot-sha256',SNAP_SHA,'--provider-receipt',str(PROVIDER),'--provider-sha256',PROVIDER_SHA,'--foundation-input',str(FINPUT),'--expected-axiom-reports','3','--reserve-bytes',str(4*1024**3),'--budget-bytes',str(512*1024**2),'--interval','1','--grace','2']
 env=child_environment()
 proc=None;previous={};signals=[]
 def handler(sig,_):
  signals.append(sig)
  if proc is not None:
   try:os.killpg(proc.pid,signal.SIGTERM)
   except ProcessLookupError:pass
 for sig in (signal.SIGINT,signal.SIGTERM):previous[sig]=signal.signal(sig,handler)
 try:
  if signals:raise InterruptedError(('signal before pair start',signals[0]))
  proc=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,env=env,start_new_session=True)
  if signals:
   try:os.killpg(proc.pid,signal.SIGTERM)
   except ProcessLookupError:pass
  stdout,stderr=proc.communicate()
 finally:
  for sig,old in previous.items():signal.signal(sig,old)
 result={'status':'OBSERVED_PAIR_TERMINAL','command':cmd,'process_pid':proc.pid,'outer_exit_code':proc.returncode,'stdout':stdout,'stderr':stderr,'forwarded_signals':signals,'preflight_sha256':raw_sha(PREFLIGHT),'scope':'Actual paired coordinator exit and output; Foundation wrapper outer exit remains unobserved.'}
 with TERMINAL.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
 print('PAIR_TERMINAL',proc.returncode,raw_sha(TERMINAL),flush=True)
 if stdout:print(stdout,end='',flush=True)
 if stderr:print(stderr,end='',file=sys.stderr,flush=True)
 return proc.returncode if proc.returncode>=0 else 128-proc.returncode
if __name__=='__main__':raise SystemExit(main())
