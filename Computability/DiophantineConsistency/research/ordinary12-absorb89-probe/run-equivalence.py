#!/usr/bin/env python3
"""Guarded author build of the 89 bounded-port model equivalence."""
from pathlib import Path
from hashlib import sha256
import json,os,re,shutil,subprocess,sys,tempfile,time,traceback
if sys.flags.optimize:raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent;D=H.parents[1]
name=os.environ.get('ATTEMPT','attempt01')
if not re.fullmatch(r'attempt[0-9]+',name):raise SystemExit('invalid attempt')
OBS=H/'observations'/('equivalence-'+name)
if OBS.exists():raise SystemExit('refusing overwrite')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LIB=Path('/tmp/qcube92-halt-5apqi7f7/lib');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
BASE=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
BASE_PIN='8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'
PRE={
 '/tmp/direct-main-projection-kuz19y_0/Absorb89Graph.olean':'819843dbc8412f1b65691912b820d4816afa47bc6bd54b65c3ed7c3ad59a0692',
 '/tmp/direct-main-projection-c60rsgpp/Absorb89First.olean':'dccd2052e7bae80d731d316da559c842dfc00b393682fa6476c7bdc84ea5b2a8',
 '/tmp/direct-main-projection-a7he5sc3/Absorb89FirstQuotient.olean':'b722b9eb6881e6c278a78b432f7ee9b69de1218455d328b94e8af2c4e98c59e6',
 '/tmp/direct-main-projection-uhd0wsrk/Absorb89Transport.olean':'5d9c2b7aa695c3ab74366f6751f16ee8664c8ce2d33a9d1dff8697da7cdb64ba',
 '/tmp/direct-main-projection-ytn97sld/DirectMainPell.olean':'753c3774163dd16a835157cdccc71ee05f81ad81bb45ec9eaf2d612cc7710f97',
 '/tmp/direct-main-projection-dday1men/DirectMainNorm.olean':'e5f6eae350719a9b1586c21e64b974ffe70048580e2a37adc872d0a76e7965a5',
 '/tmp/direct-main-projection-zl1ey0e5/DirectMainProjection.olean':'e2510b3deeebc7d4067710ad1f3210191e6189050a9b3bfa8641f9a9a2bf3182',
 '/tmp/direct-main-projection-hxla92vq/DirectMainGraph.olean':'fc4e4c2f55ead02cd216f1225933650e9ecfec11251a76def53f886380ec3f31',
 '/tmp/free-j-qcube92-ye71qcst/XQ91.olean':'747df97728f8c8125c205a752a6a2cbe205ce243cf2612ac57614025050be17d'}
PRE['/tmp/direct-main-projection-4l10hf7o/Absorb89Growth.olean']='f9a7f3d6ba6d265cd1849c680f85452abdc54b7a411ec1e51b8e72ce1c673e77'
PRE['/tmp/direct-main-projection-bs50dqtv/Absorb89Divisibility.olean']='435632173a56e2336397c2550d03ec734f435e66d021d90c173dfad60298ae90'
PRE['/tmp/direct-main-projection-ldqctk7l/Absorb89Signs.olean']='f35548f300885a25a36dbe1aaf5977f111105da4a2720186d4755cfbbe561437'
PRE['/tmp/direct-main-projection-huxkxpj9/DirectMainPlusBranch.olean']='8c8f91302dcda3be0ecd974f54abd46c7f9af7e873786336fb4571bd75b6de04'
PRE['/tmp/direct-main-projection-1g6e1_mg/DirectMainPellGrowth.olean']='50eda5030c35ee0dc81c5d9bfc7544c5983958a028686ee405b16ae58cacff8c'
PRE['/tmp/absorb89-chain-gpc9zymd/lib/Absorb89Early.olean']='6de4fcd4e6cf992038411373bf05256caa34f6830e0da8e799ea195b9c067db1'
PRE['/tmp/absorb89-chain-gpc9zymd/lib/Absorb89Indices.olean']='33ff0966c716d34a44bd2694adcb70c7d363e9528c3fdc4f19a22b4f09763870'
PRE['/tmp/absorb89-chain-gpc9zymd/lib/Absorb89Main.olean']='cddaa25c969a1751e99dfe1387d0f2f1bcddbf556208e6cc2c50639681d97bf6'
PRE['/tmp/absorb89-chain-gpc9zymd/lib/Absorb89Oriented.olean']='50457d0ea0ec65801346f2800e131c2883fa32963af6c959afab1add8104bd5c'
PRE['/tmp/absorb89-chain-gpc9zymd/lib/Absorb89Rank.olean']='f95d999b2461551e522b0e58423b2a22377270d66f9cc1a2bddbcb9bf794181e'
PRE['/tmp/absorb89-chain-gpc9zymd/lib/Absorb89Window.olean']='5cf2a5c0a83fb22d7281ae1740c66250791a74d045ac54155efb1d6b2de3df98'
PRE['/tmp/absorb89-chain-zbhcy0_l/lib/Absorb89PositiveBranch.olean']='9e80e4ad62fd3b62fa4751dcdf44f6317b0a51a4b68bfe835674ea51d18e1625'
PRE['/tmp/absorb89-full-reflection-qiwicm6e/Absorb89ModelReflection.olean']='5f65eb40986de1bb580103f8c9b5682cbd12b7f4e4b40643c7e473f885559a55'
PRE['/tmp/absorb89-full-reflection-qtm5pp7w/Absorb89FullReflection.olean']='8def08fca9bd887b9d90cda4986449e5e0c042bcc6d143f4d62d4e0ae77439c5'
PRE['/tmp/absorb89-chain-ilcpap5k/lib/Absorb89Select.olean']='b3890a2136665108191c153a351ae5a17e4379c9a1cb08c16e436c1e1b947bf6'
PRE['/tmp/absorb89-chain-ysl2waou/lib/Absorb89Inverse.olean']='f3930a6dbd0185926e20357498aa760056d0d2d66ec9a1d72b56b9e66fab5981'
PRE['/tmp/absorb89-chain-xfx0u5_3/lib/Absorb89Forward.olean']='bbc96f8b7384d18ee871f3eb6c914180a06581ef174b5861e113911e0191d708'
NAMES=['Absorb89Equivalence']
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
