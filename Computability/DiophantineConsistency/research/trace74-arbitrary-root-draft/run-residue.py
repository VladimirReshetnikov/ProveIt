#!/usr/bin/env python3
"""HELD: run once only after independent review and coordinated release."""
import argparse,fcntl,hashlib,json,os,re,subprocess,sys,tempfile,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
BASE=Path('/tmp/trace74-direct-four-block-1zltaw2f/lib')
PARENT=Path('/tmp/trace74-guardfree-pell-jg0_m3mj')
GRAND=Path('/tmp/trace74-arbitrary-root-wppvu6hp/lib')
CORE=LEAN.parent.parent/'lib/lean'
PINS={H/'Trace74FirstIndexResidue.lean':'5454d0e46d9e89800a96203ff244c23dae6dc2dab2737defa3587b52156fc9ce',H/'pell-observations/attempt01/terminal.json':'7f4510e88c09a82d0094ab3b759fdc483994c10c833c99a6ec2e8927ba09c7f8',PARENT/'Trace74Pell.olean':'9d4091ba1b0de184e0d454eb3dc1f5f3bf0810e1ddd08d186dfd550cb44fe3d0',GRAND/'Trace74GraphRoots.olean':'416dd86090bca9dc40d2dcf2836c58a9c512357a142d2612e2307e660347446c',GRAND/'Trace74ArbitraryRoot.olean':'d88173c17426e26d8f058cc45ac48ce85c64c7908afea6986fba42b42032aa55',GRAND/'Trace74ArbitraryRootNonzero.olean':'6960690f69f6ecfdab3568fa50e9f32ca16531387715e7fb6e3a056f48dad4e6',BASE/'DiophantineConsistency/ArithmeticPellCongruences.olean':'ff395c82ca9ea770a64ec69e4b4b7f8e1e2d655d67db4831af39a2d8a78ae664',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',CORE/'Init.olean':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def resources():
 lines=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in lines if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'mem_available_kib':mem,'lean':live}
def verify():
 for p,h in PINS.items():need(sha(p)==h,'pin changed: '+str(p))
 need((BASE/'DiophantineConsistency/ArithmeticPellCongruences.olean').resolve().is_file(),'missing direct import')
def check_reports(text):
 pattern=r"\s*'Trace74FirstIndexResidue\.graph_first_index_residue' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))\s*"
 m=re.fullmatch(pattern,text,re.S)
 if not m:return False
 group=m.group(1)
 if group is None:return True
 parts=[x.strip() for x in group.split(',')]
 return bool(parts) and not any(not x for x in parts) and len(parts)==len(set(parts)) and set(parts)<={'propext','Classical.choice','Quot.sound'}
parser=argparse.ArgumentParser();parser.add_argument('--preflight-only',action='store_true');parser.add_argument('--attempt');args=parser.parse_args()
need(args.preflight_only != bool(args.attempt),'specify preflight-only or attempt')
if args.attempt:need(re.fullmatch(r'attempt[0-9]{2,}',args.attempt) is not None,'bad attempt')
verify();parent=json.loads((H/'pell-observations/attempt01/terminal.json').read_text());need(parent['status']=='PASS' and parent['object_path']==str(PARENT/'Trace74Pell.olean') and parent['object_sha256']==PINS[PARENT/'Trace74Pell.olean'],'parent record');runhash=sha(__file__);pre=resources();need(pre['mem_available_kib']>=8*1024**2 and not pre['lean'],'resource preflight')
if args.preflight_only:
 print(json.dumps({'status':'PASS','pins':{str(p):h for p,h in PINS.items()},'runner_sha256':runhash,'resources':pre,'scope':'pin and live resource preflight only; no Lean invocation'},sort_keys=True,indent=2));sys.exit(0)
lock=os.open('/tmp/direct-bfs-80-coherent-rebuild.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600);fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
verify();pre=resources();need(pre['mem_available_kib']>=8*1024**2 and not pre['lean'],'locked resource preflight')
obs=H/'residue-observations'/args.attempt;obs.mkdir(parents=True,exist_ok=False)
root=Path(tempfile.mkdtemp(prefix='trace74-guardfree-residue-'));obj=root/'Trace74FirstIndexResidue.olean'
env=os.environ.copy()
for k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'):env.pop(k,None)
env['LEAN_PATH']=str(PARENT)+':'+str(GRAND)+':'+str(BASE)+':'+str(PACK)
cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--root='+str(H),str(H/'Trace74FirstIndexResidue.lean'),'-o',str(obj)]
samples=[];reason=None;start=time.monotonic()
with (obs/'stdout').open('x') as out,(obs/'stderr').open('x') as err:
 proc=subprocess.Popen(cmd,env=env,stdout=out,stderr=err)
 try:
  while proc.poll() is None:
   time.sleep(1);s=resources();samples.append(s)
   if s['mem_available_kib']<8*1024**2 or len(s['lean'])>1:reason='resource guard';proc.kill();break
   if time.monotonic()-start>120:reason='timeout';proc.kill();break
 finally:
  if proc.poll() is None:proc.kill()
  proc.wait()
out=(obs/'stdout').read_text();err=(obs/'stderr').read_text()
valid_report=check_reports(out)
report=out if valid_report else None

verify();need(sha(__file__)==runhash,'runner changed')
status='PASS' if proc.returncode==0 and reason is None and obj.is_file() and valid_report and not err and not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',out) else 'FAIL'
result={'status':status,'command':cmd,'lean_path':env['LEAN_PATH'],'source_and_direct_pins':{str(p):h for p,h in PINS.items()},'runner_sha256':runhash,'exit':proc.returncode,'reason':reason,'preflight':pre,'postflight':resources(),'samples':samples,'elapsed':time.monotonic()-start,'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),'object_path':str(obj) if obj.exists() else None,'object_sha256':sha(obj) if obj.exists() else None,'report':report,'scope':'Guard-independent first-index residue conditional on positive 74 zero; direct inputs pinned but full project/package/dynamic ancestry and shadowing are inherited. No rank congruence, repunit, population, fixed-port guard or iPRA endpoint.'}
(obs/'terminal.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True,indent=2));sys.exit(0 if status=='PASS' else 1)
