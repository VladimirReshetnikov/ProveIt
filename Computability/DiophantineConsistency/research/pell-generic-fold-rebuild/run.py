#!/usr/bin/env python3
"""Build three generic Pell fold modules sequentially in a fresh root."""
from pathlib import Path
from hashlib import sha256
import json, os, re, shutil, subprocess, sys, tempfile, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LIB=Path('/tmp/direct90-ipra-join-b66u_qqo/lib'); PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
HALF=LIB/'DiophantineConsistency/ArithmeticPellHalfIndex.olean'
source_pins={'PellFold':'6128db9cf66a410f04df114360aa1ab887b35cecdd997b0cb805197a673c2259','PellOddFold':'5ecd8b100a2bbc9ede5d015ef25de80a0c3f887fefa7e04480c23b0ccde94ad2','PellRecovery':'8c9c824476b9bfc2431a421b2e8a9a405198ee88ff5e6f3f9b55e7268a385c47'}
pins={LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550', HALF:'6142ab8eaac6e281c3372817a6f1a8cbc14704717d4f5479c28603c754c3a4d7'}
pins.update({H/(k+'.lean'):v for k,v in source_pins.items()})
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,s):
 if not b:raise RuntimeError(s)
def res():
 ps=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines()
 lp=[x.strip() for x in ps if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean']
 mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])
 return {'lean':lp,'mem_available_kib':mem,'time_ns':time.time_ns()}
a=os.environ.get('ATTEMPT','attempt01');need(re.fullmatch(r'attempt[0-9]{2,}',a) is not None,'attempt')
out=H/'observations'/a;need(not out.exists(),'existing observation')
for p,x in pins.items():need(sha(p)==x,'pin drift '+str(p))
runner_hash=sha(__file__);pre=res();need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean'])<2,'preflight')
out.mkdir(parents=True);root=Path(tempfile.mkdtemp(prefix='pell-generic-fold-')); env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(root)+':'+str(LIB)+':'+str(PACK),'LEAN_NUM_THREADS':'1'}
stages=[]
for name in source_pins:
 for p,x in pins.items():need(sha(p)==x,'pin drift '+str(p))
 need(sha(__file__)==runner_hash,'runner changed')
 pre_stage=res();need(pre_stage['mem_available_kib']>=8*1024**2 and len(pre_stage['lean'])<2,'stage guard')
 src=root/(name+'.lean');shutil.copyfile(H/(name+'.lean'),src);shutil.copyfile(src,out/(name+'.source.txt'))
 obj=root/(name+'.olean');cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
 samples=[];reason=None;start=time.monotonic()
 with (out/(name+'.stdout')).open('x') as so,(out/(name+'.stderr')).open('x') as se:
  proc=subprocess.Popen(cmd,env=env,stdout=so,stderr=se)
  while proc.poll() is None:
   r=res();samples.append(r)
   if r['mem_available_kib']<8*1024**2 or len(r['lean'])>2:reason='resource guard';proc.terminate();break
   if time.monotonic()-start>300:reason='timeout';proc.terminate();break
   time.sleep(2)
  try:proc.wait(timeout=10)
  except subprocess.TimeoutExpired:proc.kill();proc.wait()
 log=(out/(name+'.stdout')).read_text()+(out/(name+'.stderr')).read_text()
 stage={'name':name,'command':cmd,'exit':proc.returncode,'reason':reason,'preflight':pre_stage,'samples':samples,'object_sha256':sha(obj) if obj.is_file() else None,'stdout_sha256':sha(out/(name+'.stdout')),'stderr_sha256':sha(out/(name+'.stderr'))}
 stages.append(stage)
 if proc.returncode!=0 or reason is not None or not obj.is_file() or re.search(r'(?i)(?:\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b)',log):break
for p,x in pins.items():need(sha(p)==x,'post pin drift '+str(p))
need(sha(__file__)==runner_hash,'runner changed')
result={'status':'PASS' if len(stages)==3 and all(x['exit']==0 and x['reason'] is None and x['object_sha256'] for x in stages) and not re.search(r'(?i)(?:\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b)',log) else 'FAIL','root':str(root),'lean_path':env['LEAN_PATH'],'pins':{str(p):x for p,x in pins.items()},'runner_sha256':runner_hash,'preflight':pre,'stages':stages,'postflight':res(),'scope':'fresh generic source chain, direct inputs pinned; project/package transitive and dynamic ancestry inherited'}
(out/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':result['status'],'root':str(root),'stages':[(x['name'],x['exit'],x['object_sha256']) for x in stages]}))
need(result['status']=='PASS','build failed')
