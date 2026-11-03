#!/usr/bin/env python3
"""Guarded sequential kernel checks; fresh paths, immutable evidence, no ancestry claim."""
from pathlib import Path
from hashlib import sha256
import argparse,json,os,re,shutil,subprocess,sys,time
if sys.flags.optimize:raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
CHUNK=Path('/tmp/direct-bfs-conjugacychunk-6zinidys/DirectBFSConjugacyChunk.olean')
BASE=Path('/tmp/direct-bfs-conjugacybase-ugt5d3wz/DirectBFSConjugacyBase.olean')
TABLE=Path('/tmp/direct-bfs-symbolic-kernel-2oshiby3/DirectBFSSymbolicKernel.olean')
OLD=Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/Compact943Data.olean')
RECEIPT=H.parent/'direct-bfs-lean-conjugacy-chunk-prototype/observations/directbfsconjugacychunk-attempt01/terminal.json'
MANIFEST=H/'coverage-manifest-v2.json'; GEN=H/'generate-v2.py'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
PINS={LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',CHUNK:'c5b92d5de73775bd9e0e6ef507ba903fd68d093404ab5d30bd64d0af7cdfc36d',BASE:'fd9af99e379bbb04be372433102d527633409db81f0af55b119be5f8a4dd93d2',TABLE:'69f4a2f9d32229b6846ec7f0b84fe4b4d69d5eba8de1ff5c9ddb063e1d855c3f',OLD:'9ed9ec865af1b8b3794328655ca7cb9161cb8573460c82f80c5db8c35db4bf7b',RECEIPT:'11986ad15baa72c8d85bfef57dc5c8adb1faafb7d6ba3f12036dc849ca32fa7d',MANIFEST:'d0847a6276885e969d06cf6c2f3f64b1de1f1cfba71095e35c33393630a57392',GEN:'54b48b7926b5207767380d7810806f1029dbb4ce534527cc9e318a54981d3b25'}
def need(x,msg):
 if not x:raise RuntimeError(msg)
def checkpins():
 for p,h in PINS.items():need(p.is_file() and sha(p)==h,'pin changed: '+str(p))
def resources():
 ps=subprocess.run(['ps','-eo','pid=,stat=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines()
 lp=[x.strip() for x in ps if len(x.split(None,4))>3 and x.split(None,4)[2]=='lean' and not x.split(None,4)[1].startswith('Z')]
 mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1])
 return {'lean':lp,'available_kib':mem,'time_ns':time.time_ns()}
a=argparse.ArgumentParser();a.add_argument('--attempt',required=True);a.add_argument('--output-root',required=True,type=Path);a.add_argument('--start',type=int,default=0);a.add_argument('--stop',type=int,default=59);a=a.parse_args()
need(re.fullmatch(r'[a-zA-Z0-9_-]+',a.attempt) is not None,'bad attempt')
need(0<=a.start<a.stop<=59,'bad stage range')
obs=H/'observations'/a.attempt;out=a.output_root
need(not obs.exists() and not out.exists(),'attempt/output already exists')
checkpins(); manifest=json.loads(MANIFEST.read_text());records=manifest['records'];need(len(records)==59,'bad count')
for kind,end in [('rows',943),('inverse',943),('horizontal',250),('vertical',439),('inversebounds',943),('horizontalbounds',250),('verticalbounds',439)]:
 indexes=[j for r in records for x in r['ranges'] if x['kind']==kind for j in range(x['start'],x['start']+x['count'])]
 need(indexes==list(range(end)),'bad range coverage '+kind)
for r in records:
 path=H/'chunks-v2'/(r['module']+'.lean');need(path.is_file() and sha(path)==r['source_sha256'],'chunk source changed')
receipt=json.loads(RECEIPT.read_text());need(receipt['exit']==0 and receipt['object_sha256']==PINS[CHUNK],'bad base receipt')
pathenv=receipt['lean_path'];found=next((Path(x)/'DirectBFSConjugacyChunk.olean' for x in pathenv.split(':') if (Path(x)/'DirectBFSConjugacyChunk.olean').is_file()),None)
# The proof module was the output of the sampled check and must be selected explicitly first.
pathenv=str(CHUNK.parent)+':'+pathenv
found=next((Path(x)/'DirectBFSConjugacyChunk.olean' for x in pathenv.split(':') if (Path(x)/'DirectBFSConjugacyChunk.olean').is_file()),None)
need(found is not None and found.resolve()==CHUNK.resolve() and sha(found)==PINS[CHUNK],'direct import selection')
obs.mkdir(parents=True);out.mkdir(parents=True);runnerhash=sha(Path(__file__))
(obs/'plan.json').write_text(json.dumps({'start':a.start,'stop':a.stop,'manifest_sha256':PINS[MANIFEST],'runner_sha256':runnerhash,'lean_path':pathenv,'output_root':str(out),'selected_import':{'module':'DirectBFSConjugacyChunk','path':str(CHUNK),'sha256':PINS[CHUNK]},'scope':'direct pins only; inherited project/package/dynamic source-object ancestry'},indent=2,sort_keys=True)+'\n')
for r in records[a.start:a.stop]:
 checkpins();need(sha(Path(__file__))==runnerhash,'runner changed')
 source=H/'chunks-v2'/(r['module']+'.lean');need(sha(source)==r['source_sha256'],'source changed')
 pre=resources();need(len(pre['lean'])<2 and pre['available_kib']>=8*1024**2,'resource preflight')
 need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk guard')
 stage=obs/f"stage-{r['index']:03d}";stage.mkdir();copy=out/source.name;shutil.copyfile(source,copy);shutil.copyfile(source,stage/'source.lean')
 need(sha(copy)==sha(stage/'source.lean')==r['source_sha256'],'copied source mismatch')
 obj=out/(r['module']+'.olean');cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={out}',str(copy),'-o',str(obj)]
 env={'PATH':'/usr/bin:/bin','LEAN_PATH':pathenv,'LEAN_NUM_THREADS':'1'};samples=[];reason=None;start=time.monotonic()
 with (stage/'stdout').open('x') as so,(stage/'stderr').open('x') as se:
  p=subprocess.Popen(cmd,stdout=so,stderr=se,env=env)
  try:
   while p.poll() is None:
    sample=resources();samples.append(sample)
    if len(sample['lean'])>2 or sample['available_kib']<8*1024**2:reason='resource guard';break
    if time.monotonic()-start>100:reason='timeout';break
    time.sleep(2)
  except Exception as exc:reason='monitor error '+repr(exc)
  finally:
   if reason and p.poll() is None:p.kill()
   p.wait()
 text=(stage/'stdout').read_text()+(stage/'stderr').read_text()
 reports=[f"'DirectBFSCoverage.{x['kind']}_{r['index']:03d}' does not depend on any axioms" for x in r['ranges']]
 good=(p.returncode==0 and reason is None and obj.is_file() and all(text.count(x)==1 for x in reports)
       and not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',text))
 post=resources();checkpins();need(sha(Path(__file__))==runnerhash and sha(source)==sha(copy)==sha(stage/'source.lean')==r['source_sha256'],'post-run pin changed')
 result={'module':r['module'],'ranges':r['ranges'],'command':cmd,'exit':p.returncode,'reason':reason,'elapsed':time.monotonic()-start,'accepted':good,'preflight':pre,'postflight':post,'samples':samples,'source_sha256':r['source_sha256'],'stdout_sha256':sha(stage/'stdout'),'stderr_sha256':sha(stage/'stderr'),'object_path':str(obj),'object_sha256':sha(obj) if obj.is_file() else None,'direct_import':{'module':'DirectBFSConjugacyChunk','path':str(CHUNK),'sha256':sha(CHUNK)},'runner_sha256':runnerhash}
 (stage/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({'stage':r['index'],'accepted':good,'elapsed':round(result['elapsed'],1)}),flush=True)
 need(good,'stage failed '+str(r['index']))
checkpins();need(all(sha(H/'chunks-v2'/(r['module']+'.lean'))==r['source_sha256'] for r in records),'final source changed')
summary={'status':'PASS_CHUNK_RANGE','start':a.start,'stop':a.stop,'stages':a.stop-a.start,'output_root':str(out),'manifest_sha256':PINS[MANIFEST],'runner_sha256':runnerhash,'scope':'finite checked ranges only; no aggregate model theorem or full provider ancestry'}
(obs/'result.json').write_text(json.dumps(summary,indent=2,sort_keys=True)+'\n');print(json.dumps(summary),flush=True)
