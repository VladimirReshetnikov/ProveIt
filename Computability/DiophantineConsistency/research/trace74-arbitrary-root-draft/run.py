#!/usr/bin/env python3
"""HELD: three-stage exploratory check; requires scoped review and slot release."""
import argparse,fcntl,hashlib,json,os,re,subprocess,sys,tempfile,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
BASE=Path('/tmp/trace74-direct-four-block-1zltaw2f/lib');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=LEAN.parent.parent/'lib/lean'
PINS={H/'Trace74ArbitraryRoot.lean':'f99086a72672dabd83b5f1219aabd3d8c8de555b61197df6efe3f830bd1d8a83',H/'Trace74ArbitraryRootNonzero.lean':'1d73f93a05df565eb562680fd9f1d472a4d51ba3cf4ad80585e308cf877dcc8b',H/'Trace74GraphRoots.lean':'f58087222e706c69fc04baecdeabbb36feb58a411e53e1d580cd9800b34dce14',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',CORE/'Init.olean':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e',BASE/'ProductRoot.olean':'92dbb47e969d3603f6f496f53c7995493a989293a37e5272c308ff79d3fb09d5',BASE/'Trace75Factors.olean':'1bae9331cfbca4e35cb48916f135b63eedc8b5c827f8f24ae6f12b2dff111975',BASE/'Trace74Mask.olean':'181b53fe5c5a52127a56ab25af95d0b7fda3d9842098850a70c8afc70659861e',BASE/'DiophantineConsistency/TenPositiveTrace75.olean':'1ae82441c7023e9675c5cc532d4026da6a3ee77e906996d67c315e4f693b079c',BASE/'DiophantineConsistency/ModelDifferenceRing.olean':'d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74'}
STAGES=[('Trace74ArbitraryRoot','Trace74ArbitraryRoot.roots_of_representatives'),('Trace74ArbitraryRootNonzero','Trace74ArbitraryRootNonzero.roots_of_positive_representatives'),('Trace74GraphRoots','Trace74GraphRoots.graph_roots')]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def resources():
 lines=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in lines if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'mem_available_kib':mem,'lean':live}
def verify():
 for p,h in PINS.items():need(sha(p)==h,'pin changed: '+str(p))
def report_ok(text,name):
 pat=r"\s*'"+re.escape(name)+r"' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))\s*"
 m=re.fullmatch(pat,text,re.S)
 if not m:return False
 group=m.group(1)
 if group is None:return True
 parts=[x.strip() for x in group.split(',')]
 return bool(parts) and not any(not x for x in parts) and len(parts)==len(set(parts)) and set(parts)<={'propext','Classical.choice','Quot.sound'}
parser=argparse.ArgumentParser();parser.add_argument('--preflight-only',action='store_true');parser.add_argument('--attempt');args=parser.parse_args()
need(args.preflight_only != bool(args.attempt),'specify preflight-only or attempt')
if args.attempt:need(re.fullmatch(r'attempt[0-9]{2,}',args.attempt) is not None,'bad attempt')
verify();runhash=sha(__file__);pre=resources();need(pre['mem_available_kib']>=8*1024**2 and not pre['lean'],'resource preflight')
if args.preflight_only:
 print(json.dumps({'status':'PASS','pins':{str(p):h for p,h in PINS.items()},'runner_sha256':runhash,'resources':pre,'scope':'pin and live resource preflight only; no Lean invocation'},sort_keys=True,indent=2));sys.exit(0)
lock=os.open('/tmp/direct-bfs-80-coherent-rebuild.lock',os.O_RDWR|os.O_CREAT|os.O_NOFOLLOW,0o600);fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
verify();pre=resources();need(pre['mem_available_kib']>=8*1024**2 and not pre['lean'],'locked resource preflight')
obs=H/'observations'/args.attempt;obs.mkdir(parents=True,exist_ok=False);root=Path(tempfile.mkdtemp(prefix='trace74-arbitrary-root-'));lib=root/'lib';lib.mkdir()
env=os.environ.copy()
for k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'):env.pop(k,None)
env['LEAN_PATH']=str(lib)+':'+str(BASE)+':'+str(PACK)
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
result={'status':overall,'runner_sha256':runhash,'pins':{str(p):h for p,h in PINS.items()},'lean_path':env['LEAN_PATH'],'preflight':pre,'postflight':resources(),'stages':records,'output_root':str(root),'scope':'Exploratory arbitrary difference-ring 75 valuation root extraction and 74 graph client. Direct objects pinned; full project/package/dynamic ancestry and search-path shadowing remain inherited; no fixed-port guard, population, or iPRA theorem.'}
(obs/'terminal.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True,indent=2));sys.exit(0 if overall=='PASS' else 1)
