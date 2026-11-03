#!/usr/bin/env python3
"""Build three generic carrier transport modules sequentially in a fresh root."""
from pathlib import Path
from hashlib import sha256
import json, os, re, shutil, subprocess, sys, tempfile, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('use python3 -I -S -B')
H=Path(__file__).resolve().parent
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LIB=Path('/tmp/direct90-ipra-join-b66u_qqo/lib'); PACK=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
HALF=LIB/'DiophantineConsistency/ArithmeticGcdNormalization.olean'
MODEL=LIB/'DiophantineConsistency/ModelDifferenceRing.olean'
LINARITH=PACK/'Mathlib/Tactic/Linarith.olean'
source_pins={'TransportOrder':'3d3e258b0f71f411a2601993184448f1be3b49cb256904d434e28f0ba141d62a','CarrierTransport':'81bc9525bc97da98e94040230090795ff2fa56ba4faade8fc16567e06b84c7cc','OffsetBound':'696900c026b495235e88def39125f56b774341f1ed6ddd5aaccc5a9d0080525b'}
pins={LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550', HALF:'254b88abe787829f8bfad61f9606a14318cb31186b593e0cb76821e4e1ad1242',MODEL:'d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74',LINARITH:'bbe0c9d1f3d5471ae115ccd10d9ef2f6dc5ec645bad49ee5a04830c178e42091'}
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
out.mkdir(parents=True);root=Path(tempfile.mkdtemp(prefix='generic-transport-')); env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(root)+':'+str(LIB)+':'+str(PACK),'LEAN_NUM_THREADS':'1'}
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
result={'status':'PASS' if len(stages)==3 and all(x['exit']==0 and x['reason'] is None and x['object_sha256'] for x in stages) and not re.search(r'(?i)(?:\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b)',log) else 'FAIL','root':str(root),'lean_path':env['LEAN_PATH'],'pins':{str(p):x for p,x in pins.items()},'runner_sha256':runner_hash,'preflight':pre,'stages':stages,'postflight':res(),'scope':'fresh generic transport source chain; selected direct inputs pinned; project/package transitive and dynamic ancestry inherited'}
(out/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':result['status'],'root':str(root),'stages':[(x['name'],x['exit'],x['object_sha256']) for x in stages]}))
need(result['status']=='PASS','build failed')
