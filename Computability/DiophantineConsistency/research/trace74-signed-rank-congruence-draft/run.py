#!/usr/bin/env python3
"""HELD: run once only after independent review and coordinated release."""
import argparse,fcntl,hashlib,json,os,re,subprocess,sys,tempfile,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
BASE=Path('/tmp/trace74-direct-four-block-1zltaw2f/lib')
OFFSET=Path('/tmp/trace74-guardfree-offset-g91osrrh/lib');RESIDUE=Path('/tmp/trace74-guardfree-residue-9rz_sl3r');PELL=Path('/tmp/trace74-guardfree-pell-jg0_m3mj');ADJ=Path('/tmp/trace74-guardfree-adjacent-e85cpupi/lib');ROOTS=Path('/tmp/trace74-arbitrary-root-wppvu6hp/lib')
CORE=LEAN.parent.parent/'lib/lean'
PINS={H/'Trace74SignedRankCongruence.lean':'6663031030a63a1cce44cea143c5801457912316441ac4a6a68ba2d2475398da',H.parent/'trace74-guardfree-adjacent-draft/offset-observations/attempt03/terminal.json':'8152cf17eafb3f2520a7063e8de1e8814894bc9215575dfe135f4260410e0ca9',H.parent/'trace74-arbitrary-root-draft/residue-observations/attempt01/terminal.json':'3c7ed7084bbe5528b768de2084271d0293e7b5fd247410450da59c1d83e0c4f3',OFFSET/'Trace74OffsetDiv.olean':'8cda6ba55de79fb4cff0d0e0db73c84d2b31243412dd72c02c5c2ca7956e7b9e',OFFSET/'Trace74CarrierBound.olean':'dd0e99f93eced01bf479592d2c9a76efc86b29d3a17b28c2daede3ed5719c8e4',RESIDUE/'Trace74FirstIndexResidue.olean':'9155e2a4d9a945750f1edb1af9ce985d4b6f5ff55323b68a82a83ec3724d288f',PELL/'Trace74Pell.olean':'9d4091ba1b0de184e0d454eb3dc1f5f3bf0810e1ddd08d186dfd550cb44fe3d0',ADJ/'Trace74Representatives.olean':'ea48131f0f0ec2d4e7d3a3fea37e9b4cb676b7e6e2eb1a296c8573247979d86e',ADJ/'Trace74Adjacent.olean':'f3a04fb5e9368c1bf3b663b059c0a82818256e0f09b036c493bde6906b4323b5',ADJ/'Trace74Residue.olean':'35146b81c45e7a2f88debb74b3fbf1c47571f7644905f6a820a2cea616e723cc',ROOTS/'Trace74GraphRoots.olean':'416dd86090bca9dc40d2dcf2836c58a9c512357a142d2612e2307e660347446c',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',CORE/'Init.olean':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def resources():
 lines=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in lines if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'mem_available_kib':mem,'lean':live}
def verify():
 for p,h in PINS.items():need(sha(p)==h,'pin changed: '+str(p))
 need((OFFSET/'Trace74OffsetDiv.olean').resolve().is_file() and (RESIDUE/'Trace74FirstIndexResidue.olean').resolve().is_file(),'missing direct import')
def check_reports(text):
 names=['signed_dvd_of_mod_eq','graph_signed_rank_congruence']
 prefix=r"'Trace74SignedRankCongruence\.%s' "
 body=r"(?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))"
 m=re.fullmatch(r"\s*"+prefix%names[0]+body+r"\s*"+prefix%names[1]+body+r"\s*",text,re.S)
 if not m:return False
 for group in (m.group(1),m.group(3)):
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
obs=H/'lean-observations'/args.attempt;obs.mkdir(parents=True,exist_ok=False)
root=Path(tempfile.mkdtemp(prefix='trace74-signed-rank-'));obj=root/'Trace74SignedRankCongruence.olean'
env=os.environ.copy()
for k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'):env.pop(k,None)
env['LEAN_PATH']=':'.join(map(str,(OFFSET,RESIDUE,PELL,ADJ,ROOTS,BASE,PACK)))
cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--root='+str(H),str(H/'Trace74SignedRankCongruence.lean'),'-o',str(obj)]
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
result={'status':status,'command':cmd,'lean_path':env['LEAN_PATH'],'source_and_direct_pins':{str(p):h for p,h in PINS.items()},'runner_sha256':runhash,'exit':proc.returncode,'reason':reason,'preflight':pre,'postflight':resources(),'samples':samples,'elapsed':time.monotonic()-start,'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),'object_path':str(obj) if obj.exists() else None,'object_sha256':sha(obj) if obj.exists() else None,'report':report,'scope':'Signed rank and first-index congruence for positive 74 graph zero; direct objects pinned, project/package/dynamic ancestry and path shadowing inherited. No natural rank or bound, fixed-port guard or iPRA endpoint.'}
(obs/'terminal.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True,indent=2));sys.exit(0 if status=='PASS' else 1)
