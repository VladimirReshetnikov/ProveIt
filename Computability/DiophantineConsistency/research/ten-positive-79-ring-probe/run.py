#!/usr/bin/env python3
"""Check the explicit 80 register expressions against Direct80Graph."""
from hashlib import sha256
from pathlib import Path
import json,os,re,shutil,subprocess,sys,tempfile,time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent;SRC=H/'MaskCoordinate79.lean';attempt=os.environ.get('ATTEMPT','attempt01')
if re.fullmatch(r'attempt[0-9]{2,}',attempt) is None:raise SystemExit('invalid attempt')
O=H/'observations'/attempt
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');GRAPH=Path('/tmp/tenpositive-80graph-d2v79zbc/Direct80Graph.olean')
LIB=Path('/tmp/direct90-ipra-join-b66u_qqo/lib');PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def resources():
 ps=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines()
 rows=[x.strip() for x in ps if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean']
 mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])
 return {'time_ns':time.time_ns(),'lean':rows,'mem_available_kib':mem}
need(not O.exists(),'observation exists')
need(sha(SRC)=='d017edeccda26a8c605dd0da90d99ea599b5bcb47d32b19f977818ab689d4b9d','source drift')
need(sha(GRAPH)=='95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4','graph drift')
need(sha(LEAN)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','Lean drift')
pre=resources();need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'resource guard')
O.mkdir(parents=True);root=Path(tempfile.mkdtemp(prefix='mask79-ring-'));source=root/'MaskCoordinate79.lean';shutil.copyfile(SRC,source);shutil.copyfile(SRC,O/'source.txt')
cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(source),'-o',str(root/'MaskCoordinate79.olean')]
env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(GRAPH.parent)+':'+str(LIB)+':'+str(PACK),'LEAN_NUM_THREADS':'1'}
samples=[];reason=None;start=time.monotonic()
with (O/'stdout').open('x') as so,(O/'stderr').open('x') as se:
 p=subprocess.Popen(cmd,env=env,stdout=so,stderr=se)
 while p.poll() is None:
  s=resources();samples.append(s)
  if s['mem_available_kib']<8*1024**2 or len(s['lean'])>2:reason='resource guard';p.terminate();break
  if time.monotonic()-start>300:reason='timeout';p.terminate();break
  time.sleep(2)
 try:p.wait(timeout=10)
 except subprocess.TimeoutExpired:p.kill();p.wait()
need(sha(GRAPH)=='95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4' and sha(SRC)==sha(source),'input changed')
obj=root/'MaskCoordinate79.olean';text=(O/'stdout').read_text()+(O/'stderr').read_text()
result={'command':cmd,'lean_path':env['LEAN_PATH'],'exit':p.returncode,'reason':reason,'output_root':str(root),
 'source_sha256':sha(SRC),'graph':{'path':str(GRAPH),'sha256':sha(GRAPH)},'runner_sha256':sha(H/'run.py'),
 'preflight':pre,'samples':samples,'postflight':resources(),'stdout_sha256':sha(O/'stdout'),'stderr_sha256':sha(O/'stderr'),
 'object_sha256':sha(obj) if obj.is_file() else None,'scope':'formal explicit Lean row expression versus selected graph object; external file correspondence and transitive ancestry inherited'}
(O/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({'exit':p.returncode,'reason':reason,'root':str(root),'object_sha256':result['object_sha256']}))
need(p.returncode==0 and reason is None and obj.is_file() and not re.search(r'(?i)(?:\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b)',text),'Lean check failed')
