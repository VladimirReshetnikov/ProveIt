#!/usr/bin/env python3
"""HELD: single-stage exploratory check; requires scoped review and slot release."""
import argparse,fcntl,hashlib,json,os,re,subprocess,sys,tempfile,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');CORE=LEAN.parent.parent/'lib/lean'
LO=Path('/tmp/trace74-n6-r11-scalar-h80u7iit/lib');UP=Path('/tmp/trace74-n6-r11-upper-compact-v4-0up3vfpa/lib')
PINS={H/'Trace74N6R11Scalar.lean':'ee4aab43eff285cf5332c70f703139942115e028f1a312182cdf6311b48e2bba',H/'check_selection.py':'696afa0aae9bbbfa328f5ac89615cc96ffb291eb56879dcedf6d548c409ebb0b',H/'selection.json':'354453e813c245242a41c456a1eeb8cd1a5e274c63d2cbe45f0411ceaea1b20b',H.parent/'trace74-n6-r11-scalar-draft/observations/attempt01/terminal.json':'312637f58af3a713267a282967df0cbded2b27fa9a75e03f7c174db1018b40d6',H.parent/'trace74-n6-r11-upper-compact-draft-v4/observations/attempt01/terminal.json':'c755bc4ae693037fec8773824d44645d91e4ad54537d19885a7dd1ae624cdd00',LO/'Trace74N6R11LowerCertificate.olean':'63c4a37943ff1872822934b47b4970f388f6d0a79f40b751c6e07f81d246de96',UP/'Trace74N6R11CompactUpper.olean':'cae7a590b48d4475b470a1f5a429cc9533b58bdeb02870b3b9fbccf88207821f',UP/'Trace74N6R11CompactBase.olean':'960d185dddc1b1a7494c8292e2423e4d38c0536ef43bd37df4ae87705f325411',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',CORE/'Init.olean':'d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e',PACK/'Mathlib/Algebra/Order/Ring/Basic.olean':'ea83b1b21091681e446b6d29768b758db2523188f511a372f599db4d4f2d9333',PACK/'Mathlib/Tactic/Ring.olean':'cc12dfa66db7ef6ae4cd2d7a4e035ddffaca827168243f728812776b77836eb4',PACK/'Mathlib/Tactic/Linarith.olean':'bbe0c9d1f3d5471ae115ccd10d9ef2f6dc5ec645bad49ee5a04830c178e42091',PACK/'Mathlib/Tactic/Positivity.olean':'2cc0157fed7329f829258ec4d02d8a507b75db2dbe35836992c0781ab860f91c'}
STAGES=[('Trace74N6R11Scalar',['Trace74N6R11Scalar.no_scalar_solution'])]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def resources():
 lines=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in lines if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'mem_available_kib':mem,'lean':live}
def verify():
 for p,h in PINS.items():need(sha(p)==h,'pin changed: '+str(p))
 sel=subprocess.run([sys.executable,'-I','-S','-B',str(H/'check_selection.py')],capture_output=True);need(sel.returncode==0 and sel.stdout==(H/'selection.json').read_bytes() and not sel.stderr,'direct first-selection mismatch')
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
obs=H/'observations'/args.attempt;obs.mkdir(parents=True,exist_ok=False);root=Path(tempfile.mkdtemp(prefix='trace74-n6-r11-scalar-compact-'));lib=root/'lib';lib.mkdir()
env=os.environ.copy()
for k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'):env.pop(k,None)
env['LEAN_PATH']=':'.join(map(str,(lib,LO,UP,PACK)))
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
result={'status':overall,'runner_sha256':runhash,'pins':{str(p):h for p,h in PINS.items()},'lean_path':env['LEAN_PATH'],'preflight':pre,'postflight':resources(),'stages':records,'output_root':str(root),'scope':'Conditional discrete scalar contradiction only; lower is an audited passed stage from a failed run; no graph binding. Current direct source-import first selections checked; serialized transitive/package and producer-time ancestry remain inherited. Direct objects pinned; full project/package/dynamic ancestry and search-path shadowing remain inherited; no fixed-port guard, population, or iPRA theorem.'}
(obs/'terminal.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,sort_keys=True,indent=2));sys.exit(0 if overall=='PASS' else 1)
