#!/usr/bin/env python3
"""Guarded author build of the 80 radix-square coprimality certificate."""
from pathlib import Path
from hashlib import sha256
import json,os,re,shutil,subprocess,sys,tempfile,time,traceback
if sys.flags.optimize:raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent;D=H.parents[1]
name=os.environ.get('ATTEMPT','attempt01')
if not re.fullmatch(r'attempt[0-9]+',name):raise SystemExit('invalid attempt')
OBS=H/'observations'/('coprime-'+name)
if OBS.exists():raise SystemExit('refusing overwrite')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LIB=Path('/tmp/qcube92-halt-5apqi7f7/lib');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
BASE=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
BASE_PIN='8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'
PRE={'/tmp/qcube92-halt-5apqi7f7/lib/DiophantineConsistency/ArithmeticPellPowerRecovery.olean':'81ac9f2d4ffcf1ad8a5bce697cc6369a21a1df07aa9fdf10a8700e63755e392f'}
PRE['/tmp/absorb89-chain-dthpavjy/lib/Direct80Parity.olean']='4e09228842b503bba133bd98da8670e5ff5983a6fdd23cc15c293e71159c065f'
NAMES=['Direct80Coprime']
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise RuntimeError(m)
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'non-file '+str(p));return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
def resources():
 ps=[]
 for p in Path('/proc').iterdir():
  if not p.name.isdigit():continue
  try:e=(p/'exe').resolve(strict=True)
  except (OSError,RuntimeError):continue
  if e==LEAN.resolve(strict=True):ps.append(int(p.name))
 m=next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
 return {'time_ns':time.time_ns(),'mem_available_kib':int(m.split()[1]),'lean_pids':sorted(ps)}
def inventory(base):
 a={p.relative_to(LIB).as_posix():rec(p) for p in LIB.rglob('*') if p.is_file()}
 need(len(a)==1291 and a==base['union'],'provider drift');return a
def predecessors():
 for p,h in PRE.items():need(Path(p).is_file() and sha(p)==h,'predecessor drift '+p)
def main():
 need(sha(BASE)==BASE_PIN,'base receipt drift');base=json.loads(BASE.read_text());before=inventory(base);predecessors()
 need(sha(LEAN)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','Lean drift')
 sources={n:sha(H/(n+'.lean')) for n in NAMES};runner=sha(__file__)
 OBS.mkdir(parents=True);tmp=Path(tempfile.mkdtemp(prefix='absorb89-chain-'));out=tmp/'lib';src=tmp/'src';out.mkdir();src.mkdir()
 paths=[str(out)]+[str(Path(p).parent) for p in PRE]+[str(LIB),str(PACKAGE)]
 env={'PATH':'/usr/bin:/bin','LEAN_PATH':':'.join(paths),'LEAN_NUM_THREADS':'1'}
 result={'status':'FAILED','output_root':str(tmp),'sources':sources,'runner_sha256':runner,'predecessors':PRE,
  'lean_path':env['LEAN_PATH'],'stages':[],'scope':'selected project author chain; package/dynamic/source-object ancestry inherited; no reverse or iPRA theorem'}
 try:
  outputs={}
  for i,n in enumerate(NAMES,1):
   pre=resources();need(pre['mem_available_kib']>=8*1024**2 and len(pre['lean_pids'])<2,'resource preflight')
   s=H/(n+'.lean');sp=src/(n+'.lean');op=out/(n+'.olean');shutil.copyfile(s,sp);shutil.copyfile(s,OBS/(f'stage-{i:02}.source.lean'))
   need(sha(sp)==sources[n],'source copy');cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={src}',str(sp),'-o',str(op)]
   samples=[];reason=None;start=time.monotonic();so=OBS/(f'stage-{i:02}.stdout');se=OBS/(f'stage-{i:02}.stderr')
   with so.open('xb') as f,se.open('xb') as e:
    proc=subprocess.Popen(cmd,env=env,stdout=f,stderr=e)
    try:
     while proc.poll() is None:
      snap=resources();samples.append(snap)
      if snap['mem_available_kib']<8*1024**2 or len(snap['lean_pids'])>2:reason='resource guard';break
      if time.monotonic()-start>180:reason='timeout';break
      time.sleep(1)
    except Exception as exc:reason='monitor exception '+repr(exc)
    finally:
     if reason and proc.poll() is None:proc.kill()
     proc.wait()
   row={'module':n,'command':cmd,'exit':proc.returncode,'reason':reason,'elapsed':time.monotonic()-start,'preflight':pre,'samples':samples,
        'source_sha256':sources[n],'stdout_sha256':sha(so),'stderr_sha256':sha(se),'object_sha256':sha(op) if op.is_file() else None}
   (OBS/(f'stage-{i:02}.json')).write_text(json.dumps(row,indent=2,sort_keys=True)+'\n');result['stages'].append(row)
   text=so.read_text()+se.read_text()
   need(proc.returncode==0 and reason is None and op.is_file() and not re.search(r'\b(?:error|warning)(?:\([^\n)]*\))?:',text) and 'sorryAx' not in text,'stage failure '+n)
   need(sha(s)==sha(sp)==sources[n],'source changed');outputs[n]=sha(op)
   need(inventory(base)==before,'union changed');predecessors()
   for prev,h in outputs.items():need(sha(out/(prev+'.olean'))==h,'output drift '+prev)
  need(sha(__file__)==runner and sha(BASE)==BASE_PIN,'runner/base changed');result['status']='PASS'
 except Exception as e:result['error']=repr(e);result['traceback']=traceback.format_exc()
 (OBS/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':result['status'],'error':result.get('error'),'output_root':str(tmp),'stages':len(result['stages'])}))
 if result['status']!='PASS':raise SystemExit(1)
if __name__=='__main__':main()
