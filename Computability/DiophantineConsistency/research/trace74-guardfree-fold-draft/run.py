#!/usr/bin/env python3
"""HELD: three-stage exploratory check; requires scoped review and slot release."""
import argparse,fcntl,hashlib,json,os,re,subprocess,sys,tempfile,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
ADJ=Path('/tmp/trace74-guardfree-adjacent-e85cpupi/lib');PELL=Path('/tmp/trace74-guardfree-pell-jg0_m3mj');ROOTS=Path('/tmp/trace74-arbitrary-root-wppvu6hp/lib');BASE=Path('/tmp/trace74-direct-four-block-1zltaw2f/lib');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=LEAN.parent.parent/'lib/lean'
PINS={H/'Trace74Joined.lean':'bc2558cbffd2fbf0f118488825366c893439f1cd13d1ac818da2628ecf98d16e',H/'Trace74Fold.lean':'27fdb1e75e0dde20e132f37bb8eb117a5b7090de8eb5f8153c042368568810ae',H/'Trace74Index.lean':'e2f115c4516c851242a145c95024bdf57326e5907e25f4c01b401ac4c78f3a26',H/'Trace74Size.lean':'2a3628b59b3fe4de7d4f1f380c38caff73831ad78aebf5199a7d56021475d37a',H.parent/'trace74-guardfree-adjacent-draft/observations/attempt03/terminal.json':'f448f68d4c0b47a5409e77b91a67535c0f54cc78d91dbba25979a421b85c7a09',H.parent/'trace74-arbitrary-root-draft/pell-observations/attempt01/terminal.json':'7f4510e88c09a82d0094ab3b759fdc483994c10c833c99a6ec2e8927ba09c7f8',ADJ/'Trace74Representatives.olean':'ea48131f0f0ec2d4e7d3a3fea37e9b4cb676b7e6e2eb1a296c8573247979d86e',ADJ/'Trace74Adjacent.olean':'f3a04fb5e9368c1bf3b663b059c0a82818256e0f09b036c493bde6906b4323b5',ADJ/'Trace74Residue.olean':'35146b81c45e7a2f88debb74b3fbf1c47571f7644905f6a820a2cea616e723cc',PELL/'Trace74Pell.olean':'9d4091ba1b0de184e0d454eb3dc1f5f3bf0810e1ddd08d186dfd550cb44fe3d0',ROOTS/'Trace74GraphRoots.olean':'416dd86090bca9dc40d2dcf2836c58a9c512357a142d2612e2307e660347446c',BASE/'PellRecovery.olean':'0deec819d3d49c3ebfe8179175613095e6497272cfc6cc1d7723c8df6b32524a',BASE/'Direct80IndexOne.olean':'f439752ad98d0b0c2f1ece874cfd46d4a340f84d34a9dd644e95910bf4d14db7',BASE/'DiophantineConsistency/ArithmeticPellHalfIndex.olean':'6142ab8eaac6e281c3372817a6f1a8cbc14704717d4f5479c28603c754c3a4d7',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',CORE/'Init.olean':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e'}
STAGES=[('Trace74Joined',['Trace74Joined.strong_and_auxiliary_indices_with_graph_residue']),('Trace74Fold',['Trace74Fold.graph_odd_ordinate']),('Trace74Index',['Trace74Index.first_index_ge_two']),('Trace74Size',['Trace74Size.graph_rank_size'])]
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
obs=H/'observations'/args.attempt;obs.mkdir(parents=True,exist_ok=False);root=Path(tempfile.mkdtemp(prefix='trace74-guardfree-fold-'));lib=root/'lib';lib.mkdir()
env=os.environ.copy()
for k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'):env.pop(k,None)
env['LEAN_PATH']=':'.join(map(str,(lib,ADJ,PELL,ROOTS,BASE,PACK)))
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
result={'status':overall,'runner_sha256':runhash,'pins':{str(p):h for p,h in PINS.items()},'lean_path':env['LEAN_PATH'],'preflight':pre,'postflight':resources(),'stages':records,'output_root':str(root),'scope':'Exploratory guard-independent 74 odd ordinate, first-index lower bound and size consequences. Direct objects pinned; full project/package/dynamic ancestry and search-path shadowing remain inherited; no fixed-port guard, population, or iPRA theorem.'}
(obs/'terminal.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True,indent=2));sys.exit(0 if overall=='PASS' else 1)
