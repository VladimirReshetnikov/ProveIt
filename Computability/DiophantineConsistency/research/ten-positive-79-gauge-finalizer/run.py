#!/usr/bin/env python3
"""Bounded check of the generic 79 gauge algebra."""
from pathlib import Path
from hashlib import sha256
import json,os,re,subprocess,sys,tempfile,time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
h=Path(__file__).resolve().parent;lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');src=h/'Mask79Finalizer.lean';provider=Path('/tmp/mask79-carrier-w290b5ah/Mask79Carrier.olean');mathlib=pkg/'Mathlib/Tactic/Ring.olean'
pins={lean:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',src:'a20dbdf0f0cabaa10921485f2f4c27c7948a8b63d7a5b67f7cc17ea52b1fc926',provider:'a880a3df700be3af796282b0600161756e640ad7da78fdcb383fa49b1c2f5b60',mathlib:'cc12dfa66db7ef6ae4cd2d7a4e035ddffaca827168243f728812776b77836eb4'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def resources():
 ps=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in ps if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'lean':live,'mem_available_kib':mem}
for p,d in pins.items():need(sha(p)==d,'pin mismatch '+str(p))
need(re.findall(r'^import\s+(\S+)',src.read_text(),re.M)==['Mask79Carrier'],'direct import mismatch')
a=os.environ.get('ATTEMPT','attempt01');need(re.fullmatch(r'attempt\d\d+',a),'attempt name');obs=h/'observations'/a;need(not os.path.lexists(obs),'observation exists');obs.mkdir(parents=True)
pre=resources();need(len(pre['lean'])<2 and pre['mem_available_kib']>=8*1024**2,'resource preflight')
out=Path(tempfile.mkdtemp(prefix='mask79-finalizer-'));target=out/'Mask79Finalizer.olean';command=[str(lean),'-M3000','-j1','-DElab.async=false',str(src),'-o',str(target)];env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(provider.parent)+':'+str(pkg)};start=time.monotonic();samples=[];reason=None
with (obs/'stdout').open('x') as so,(obs/'stderr').open('x') as se:
 p=subprocess.Popen(command,env=env,stdout=so,stderr=se)
 while p.poll() is None:
  sample=resources();samples.append(sample)
  if len(sample['lean'])>2 or sample['mem_available_kib']<8*1024**2:reason='resource guard';p.terminate();break
  if time.monotonic()-start>180:reason='timeout';p.terminate();break
  time.sleep(2)
 try:p.wait(timeout=10)
 except subprocess.TimeoutExpired:p.kill();p.wait()
text=(obs/'stdout').read_text()+(obs/'stderr').read_text();ok=p.returncode==0 and reason is None and target.is_file() and not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',text)
pat=r"'Mask79Finalizer.preserve_output' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)";matches=re.findall(pat,text,re.S);ok=ok and len(matches)==1 and set(x.strip() for x in matches[0].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
for path,d in pins.items():need(sha(path)==d,'pin changed during run '+str(path))
record={'status':'PASS' if ok else 'FAILED','command':command,'exit':p.returncode,'reason':reason,'elapsed':time.monotonic()-start,'source_sha256':sha(src),'runner_sha256':sha(Path(__file__)),'pins':{str(k):{'sha256':v,'resolved':str(k.resolve())} for k,v in pins.items()},'output':str(target),'output_sha256':sha(target) if target.is_file() else None,'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),'preflight':pre,'samples':samples,'postflight':resources(),'scope':'abstract finalizer identity; graph evaluation, positivity and normalization excluded'}
(obs/'terminal.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':record['status'],'exit':record['exit'],'output':record['output'],'output_sha256':record['output_sha256']}));raise SystemExit(0 if ok else 1)
