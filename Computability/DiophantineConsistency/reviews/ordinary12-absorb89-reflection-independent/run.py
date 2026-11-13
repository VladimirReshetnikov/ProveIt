#!/usr/bin/env python3
"""Bounded Lean check of the conditional 89-row reflection result."""
from hashlib import sha256
import json,os,shutil,subprocess,sys,tempfile,time
from pathlib import Path
if sys.flags.optimize:raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent;D=H.parents[1]
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LIB=Path('/tmp/qcube92-halt-5apqi7f7/lib')
BASE=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
SRC=H/'Absorb89FullReflection.lean';attempt=os.environ.get('ATTEMPT','attempt01')
if not attempt.startswith('attempt') or not attempt[7:].isdigit():raise SystemExit('bad attempt')
OBS=H/'observations'/attempt
if OBS.exists():raise SystemExit('existing observation')
PINS={BASE:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f',
 LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
 Path('/tmp/direct-main-projection-c60rsgpp/Absorb89First.olean'):'dccd2052e7bae80d731d316da559c842dfc00b393682fa6476c7bdc84ea5b2a8',
 Path('/tmp/direct-main-projection-kuz19y_0/Absorb89Graph.olean'):'819843dbc8412f1b65691912b820d4816afa47bc6bd54b65c3ed7c3ad59a0692',
 Path('/tmp/direct-main-projection-hxla92vq/DirectMainGraph.olean'):'fc4e4c2f55ead02cd216f1225933650e9ecfec11251a76def53f886380ec3f31',
 Path('/tmp/free-j-qcube92-ye71qcst/XQ91.olean'):'747df97728f8c8125c205a752a6a2cbe205ce243cf2612ac57614025050be17d'}
def need(x,msg):
 if not x:raise RuntimeError(msg)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'non-file '+str(p));return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
def resources():
 pids=[]
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:exe=(p/'exe').resolve(strict=True)
  except (OSError,RuntimeError):continue
  if exe==LEAN.resolve(strict=True):pids.append(int(p.name))
 row=next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
 return {'mem_available_kib':int(row.split()[1]),'lean_pids':sorted(pids),'time_ns':time.time_ns()}
def inventory(expected):
 result={p.relative_to(LIB).as_posix():rec(p) for p in LIB.rglob('*') if p.is_file()}
 need(len(result)==1291 and result==expected,'selected union drift');return result
for p,h in PINS.items():need(sha(p)==h,'input pin '+str(p))
base=json.loads(BASE.read_text());need(base['exit']==0 and base['union_unchanged'],'base receipt')
before=inventory(base['union']);initial=resources()
need(initial['mem_available_kib']>=8*1024**2 and len(initial['lean_pids'])<2,'resource preflight')
need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk guard')
OBS.mkdir(parents=True);out=Path(tempfile.mkdtemp(prefix='absorb89-full-reflection-'));copy=out/SRC.name
shutil.copyfile(SRC,copy);shutil.copyfile(SRC,OBS/'source.lean');sourcehash=sha(SRC);runnerhash=sha(__file__)
paths=[Path('/tmp/direct-main-projection-c60rsgpp'),Path('/tmp/direct-main-projection-kuz19y_0'),
 Path('/tmp/direct-main-projection-hxla92vq'),Path('/tmp/free-j-qcube92-ye71qcst'),LIB,PACKAGE]
env={'PATH':'/usr/bin:/bin','LEAN_PATH':':'.join(map(str,paths)),'LEAN_NUM_THREADS':'1'}
cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={out}',str(copy),'-o',str(out/'Absorb89FullReflection.olean')]
samples=[];start=time.monotonic();reason=None
with (OBS/'stdout').open('xb') as stdout,(OBS/'stderr').open('xb') as stderr:
 proc=subprocess.Popen(cmd,env=env,stdout=stdout,stderr=stderr)
 try:
  while proc.poll() is None:
   r=resources();samples.append(r)
   if r['mem_available_kib']<8*1024**2 or len(r['lean_pids'])>2:reason='resource guard';break
   if time.monotonic()-start>180:reason='timeout';break
   time.sleep(1)
 except Exception as e:reason='monitor error '+repr(e)
 finally:
  if reason and proc.poll() is None:proc.kill()
  proc.wait()
after=inventory(base['union']);obj=out/'Absorb89FullReflection.olean'
result={'command':cmd,'lean_path':env['LEAN_PATH'],'output_root':str(out),'exit':proc.returncode,'reason':reason,
 'elapsed':time.monotonic()-start,'source_sha256':sourcehash,'source_after':sha(SRC),'runner_sha256':runnerhash,
 'runner_after':sha(__file__),'pins':{str(p):h for p,h in PINS.items()},'preflight':initial,'samples':samples,
 'object_sha256':sha(obj) if obj.is_file() else None,'union_unchanged':before==after,
 'stdout_sha256':sha(OBS/'stdout'),'stderr_sha256':sha(OBS/'stderr'),
 'scope':'conditional ring theorem, selected project provider; inherited package, dynamic and source-object ancestry'}
(OBS/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
for p,h in PINS.items():need(sha(p)==h,'changed input '+str(p))
need(proc.returncode==0 and not reason and obj.is_file() and before==after and sha(SRC)==sourcehash and sha(__file__)==runnerhash and
 not any(x in (OBS/'stdout').read_text()+(OBS/'stderr').read_text() for x in ('error:','warning:','sorryAx')),'compile failed')
print(json.dumps({k:result[k] for k in ('exit','reason','object_sha256','union_unchanged')},sort_keys=True))
