#!/usr/bin/env python3
"""HELD: single-stage exploratory check; requires scoped review and slot release."""
import argparse,fcntl,hashlib,json,os,re,subprocess,sys,tempfile,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=LEAN.parent.parent/'lib/lean'
PINS={Path(p):h for p,h in {'/tmp/absorb89-chain-nmkv9_wb/lib/Absorb88First.olean': '1332d8aa708a4f9163451dac1a6e844f3da2623b62d27e4ea952de242d2359fd', '/tmp/absorb89-chain-nmkv9_wb/lib/Absorb88FirstQuotient.olean': 'da14449292931e8f4cc35f9766af549d3c5da3d2a29a7a4d4361e27ecb2a1ba7', '/tmp/absorb89-chain-s3j20gu6/lib/Absorb88Graph.olean': 'cd20000349f683f897822be84f8675b5b117fd23fcd89eadb3f88428e170889f', '/tmp/direct-main-projection-a7he5sc3/Absorb89FirstQuotient.olean': 'b722b9eb6881e6c278a78b432f7ee9b69de1218455d328b94e8af2c4e98c59e6', '/tmp/direct-main-projection-c60rsgpp/Absorb89First.olean': 'dccd2052e7bae80d731d316da559c842dfc00b393682fa6476c7bdc84ea5b2a8', '/tmp/direct-main-projection-dday1men/DirectMainNorm.olean': 'e5f6eae350719a9b1586c21e64b974ffe70048580e2a37adc872d0a76e7965a5', '/tmp/direct-main-projection-hxla92vq/DirectMainGraph.olean': 'fc4e4c2f55ead02cd216f1225933650e9ecfec11251a76def53f886380ec3f31', '/tmp/direct-main-projection-kuz19y_0/Absorb89Graph.olean': '819843dbc8412f1b65691912b820d4816afa47bc6bd54b65c3ed7c3ad59a0692', '/tmp/direct-main-projection-uhd0wsrk/Absorb89Transport.olean': '5d9c2b7aa695c3ab74366f6751f16ee8664c8ce2d33a9d1dff8697da7cdb64ba', '/tmp/direct-main-projection-ytn97sld/DirectMainPell.olean': '753c3774163dd16a835157cdccc71ee05f81ad81bb45ec9eaf2d612cc7710f97', '/tmp/direct-main-projection-zl1ey0e5/DirectMainProjection.olean': 'e2510b3deeebc7d4067710ad1f3210191e6189050a9b3bfa8641f9a9a2bf3182', '/tmp/free-j-qcube92-ye71qcst/XQ91.olean': '747df97728f8c8125c205a752a6a2cbe205ce243cf2612ac57614025050be17d', '/tmp/absorb89-chain-y6re0ptd/lib/Absorb88Transport.olean': '94c3e0a1f4bdbd8e9777c476463099f6f6cfe9d1dd251ec06db421b906082d51', '/tmp/absorb89-chain-y6re0ptd/lib/Absorb88Signs.olean': '19111240a2efcb7fde3afa5abe93e795463aac305740e74c6f621869c67b10da', '/home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/research/ordinary12-absorb88-probe/observations/signs-attempt03/result.json': 'edcbaf30d57eaee4559bd372057f40a7799de84d9265ee6a449eb1c4bdab7ffa', '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550', '/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean/Init.olean': 'd2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e', '/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Tactic/LinearCombination.olean': 'e4487ef3e033c8a8cfe8562ee7a96d2926444bd73c7f138f265b58a8d1d14c08'}.items()}
PINS[H/'Absorb88SignedDivisibility.lean']='46fb6e2d9d3fb5b52bfdb2b709043c65c3b9bbd6b9596117109847e6e01bbef8'
PINS[Path('/tmp/qcube92-halt-5apqi7f7/lib/DiophantineConsistency/ArithmeticAdaptiveTransport2011.olean')]='beed0f0257441001571946ef8d5076b6222a0f7dc09aaa89cc12d0c58a33e64e'
STAGES=[('Absorb88SignedDivisibility',['Absorb88SignedDivisibility.signed_divisor','Absorb88SignedDivisibility.graph_signed_transport_divisibility'])]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def resources():
 lines=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in lines if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'mem_available_kib':mem,'lean':live}
def verify():
 for p,h in PINS.items():need(sha(p)==h,'pin changed: '+str(p))
def report_ok(text,names):
 body=r" (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))"
 pat=r"\s*"+r"\s*".join("'"+re.escape(n)+"'"+body for n in names)+r"\s*"
 m=re.fullmatch(pat,text,re.S)
 if not m:return False
 for i in range(len(names)):
  group=m.group(1+2*i)
  if group is None:continue
  parts=[x.strip() for x in group.split(',')]
  if not parts or any(not x for x in parts) or len(parts)!=len(set(parts)) or not set(parts)<={'propext','Classical.choice','Quot.sound'}:return False
 return True
parser=argparse.ArgumentParser();parser.add_argument('--preflight-only',action='store_true');parser.add_argument('--attempt');args=parser.parse_args()
need(args.preflight_only != bool(args.attempt),'specify preflight-only or attempt')
if args.attempt:need(re.fullmatch(r'attempt[0-9]{2,}',args.attempt) is not None,'bad attempt')
verify();runhash=sha(__file__);pre=resources();need(pre['mem_available_kib']>=8*1024**2 and not pre['lean'],'resource preflight')
if args.preflight_only:
 print(json.dumps({'status':'PASS','pins':{str(p):h for p,h in PINS.items()},'runner_sha256':runhash,'resources':pre,'scope':'pin and live resource preflight only; no Lean invocation'},sort_keys=True,indent=2));sys.exit(0)
lock=os.open('/tmp/direct-bfs-80-coherent-rebuild.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600);fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
verify();pre=resources();need(pre['mem_available_kib']>=8*1024**2 and not pre['lean'],'locked resource preflight')
obs=H/'observations'/args.attempt;obs.mkdir(parents=True,exist_ok=False);root=Path(tempfile.mkdtemp(prefix='absorb88-signed-divisibility-'));lib=root/'lib';lib.mkdir()
env=os.environ.copy()
for k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'):env.pop(k,None)
env['LEAN_PATH']=':'.join([str(lib)]+['/tmp/absorb89-chain-y6re0ptd/lib', '/tmp/direct-main-projection-kuz19y_0', '/tmp/direct-main-projection-c60rsgpp', '/tmp/direct-main-projection-a7he5sc3', '/tmp/direct-main-projection-uhd0wsrk', '/tmp/direct-main-projection-ytn97sld', '/tmp/direct-main-projection-dday1men', '/tmp/direct-main-projection-zl1ey0e5', '/tmp/direct-main-projection-hxla92vq', '/tmp/free-j-qcube92-ye71qcst', '/tmp/absorb89-chain-s3j20gu6/lib', '/tmp/absorb89-chain-nmkv9_wb/lib', '/tmp/absorb89-chain-nmkv9_wb/lib', '/tmp/qcube92-halt-5apqi7f7/lib', '/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'])
records=[];overall='PASS'
for idx,(module,report) in enumerate(STAGES,1):
 outpath=obs/f'stage-{idx:02d}.stdout';errpath=obs/f'stage-{idx:02d}.stderr';obj=lib/(module+'.olean')
 cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--root='+str(H),str(H/(module+'.lean')),'-o',str(obj)];samples=[];reason=None;start=time.monotonic()
 with outpath.open('x') as out,errpath.open('x') as err:
  proc=subprocess.Popen(cmd,env=env,stdout=out,stderr=err)
  try:
   while proc.poll() is None:
    time.sleep(1);s=resources();samples.append(s)
    if s['mem_available_kib']<8*1024**2 or len(s['lean'])>1:reason='resource guard';proc.kill();break
    if time.monotonic()-start>120:reason='timeout';proc.kill();break
  finally:
   if proc.poll() is None:proc.kill()
   proc.wait()
 out=outpath.read_text();err=errpath.read_text();ok=proc.returncode==0 and reason is None and obj.is_file() and report_ok(out,report) and not err and not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',out)
 records.append({'module':module,'expected_report':report,'status':'PASS' if ok else 'FAIL','command':cmd,'exit':proc.returncode,'reason':reason,'samples':samples,'elapsed':time.monotonic()-start,'stdout_sha256':sha(outpath),'stderr_sha256':sha(errpath),'object_path':str(obj) if obj.exists() else None,'object_sha256':sha(obj) if obj.exists() else None})
 if not ok:overall='FAIL';break
verify();need(sha(__file__)==runhash,'runner changed')
result={'status':overall,'runner_sha256':runhash,'pins':{str(p):h for p,h in PINS.items()},'lean_path':env['LEAN_PATH'],'preflight':pre,'postflight':resources(),'stages':records,'output_root':str(root),'scope':'Conditional signed transport divisibility from an actual positive 88 graph zero; no transport sign or endpoint. Direct objects pinned; full project/package/dynamic ancestry and search-path shadowing remain inherited; no fixed-port guard, population, or iPRA theorem.'}
(obs/'terminal.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True,indent=2));sys.exit(0 if overall=='PASS' else 1)
