#!/usr/bin/env python3
"""Bounded author check of conditional direct-main lemmas on the 92 provider."""
from pathlib import Path
from hashlib import sha256
import json,os,shutil,subprocess,sys,tempfile,time
if sys.flags.optimize:raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent;D=H.parents[1];a=os.environ.get('ATTEMPT','attempt01')
if not a.startswith('attempt') or not a[7:].isdigit():raise SystemExit('invalid attempt')
OBS=H/'observations'/('early-'+a)
if OBS.exists():raise SystemExit('refusing to overwrite observation')
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');LIB=Path('/tmp/qcube92-halt-5apqi7f7/lib')
BASE=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
BASE_PIN='8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'
def need(v,m):
 if not v:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 need(p.is_file(),'non-file '+str(p));return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
def resource():
 lines=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();ps=[]
 for line in lines:
  f=line.strip().split(None,3)
  if len(f)>=2 and f[1]=='lean':
   rss=int(f[2]) if len(f)>2 and f[2].isdigit() else None
   ps.append({'pid':int(f[0]),'rss_kib':rss,'args':f[3] if len(f)>3 else ' '.join(f[2:])})
 m=next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
 return {'time_ns':time.time_ns(),'mem_available_kib':int(m.split()[1]),'lean':ps}
def inventory(base):
 actual={p.relative_to(LIB).as_posix():rec(p) for p in LIB.rglob('*') if p.is_file()}
 need(len(actual)==1291 and actual==base['union'],'selected union drift');return actual
need(LEAN.is_file() and PACKAGE.is_dir(),'missing tool or package');need(shutil.disk_usage('/tmp').free>=4*1024**3,'disk guard')
need(sha(BASE)==BASE_PIN,'base receipt mismatch');base=json.loads(BASE.read_text());need(base['exit']==0 and base['union_unchanged'],'invalid base receipt')
before=inventory(base)
rank=Path('/tmp/direct-main-projection-c775ytrj/DirectMainRank.olean'); rank_pin='bf4d176eddc731e0735be39f57440d1ee991d348563e62b8aaa8ecb216f28fef'; need(rank.is_file() and sha(rank)==rank_pin,'rank producer drift')
indices=Path('/tmp/direct-main-projection-u2r3kvhj/DirectMainIndices.olean'); indices_pin='9b2e4a71257e9a6b2b151103eccdf78564a9c912e79a8a3c5113d87beb429941'; need(indices.is_file() and sha(indices)==indices_pin,'indices producer drift')
oriented=Path('/tmp/direct-main-projection-s_f4nqkk/DirectMainOriented.olean'); oriented_pin='10254beaf0ac3b44d3c65abac44c36cd0196aab6cca74ebc269a4d1b8660f521'; need(oriented.is_file() and sha(oriented)==oriented_pin,'oriented producer drift')
pell=Path('/tmp/direct-main-projection-ytn97sld/DirectMainPell.olean'); pell_pin='753c3774163dd16a835157cdccc71ee05f81ad81bb45ec9eaf2d612cc7710f97'; need(pell.is_file() and sha(pell)==pell_pin,'pell producer drift')
norm=Path('/tmp/direct-main-projection-dday1men/DirectMainNorm.olean'); norm_pin='e5f6eae350719a9b1586c21e64b974ffe70048580e2a37adc872d0a76e7965a5'; need(norm.is_file() and sha(norm)==norm_pin,'norm producer drift')
projection=Path('/tmp/direct-main-projection-zl1ey0e5/DirectMainProjection.olean'); projection_pin='e2510b3deeebc7d4067710ad1f3210191e6189050a9b3bfa8641f9a9a2bf3182'; need(projection.is_file() and sha(projection)==projection_pin,'projection producer drift')
main=Path('/tmp/direct-main-projection-wwbiv9_g/DirectMainMain.olean'); main_pin='61ff9f8218a430bc84fc39399f3ee1421c267d42c0a1a7e6cbc40f066048d17d'; need(main.is_file() and sha(main)==main_pin,'main producer drift')
transport=Path('/tmp/direct-main-projection-d1lhwfdm/DirectMainTransport.olean'); transport_pin='8cb15f06eb7f306048d084e85937d25b625356ed24d0b21ec027086543880d72'; need(transport.is_file() and sha(transport)==transport_pin,'transport producer drift')
quotient=Path('/tmp/direct-main-projection-f54kqb9e/DirectMainFirstQuotient.olean'); quotient_pin='8abb2bb6723d14abc3fadbb83e45fa067ffcc0d042110a40fc84511ef90bfee5'; need(quotient.is_file() and sha(quotient)==quotient_pin,'quotient producer drift')
first=Path('/tmp/direct-main-projection-klvywrx4/DirectMainFirst.olean'); first_pin='e24c62d66d61d09135adf82c0b3d6b9b7297fcdffddbc0582fab10dbcb35b257'; need(first.is_file() and sha(first)==first_pin,'first producer drift')
graph=Path('/tmp/direct-main-projection-hxla92vq/DirectMainGraph.olean'); graph_pin='fc4e4c2f55ead02cd216f1225933650e9ecfec11251a76def53f886380ec3f31'; need(graph.is_file() and sha(graph)==graph_pin,'graph producer drift')
producer=Path('/tmp/free-j-qcube92-ye71qcst/XQ91.olean'); producer_pin='747df97728f8c8125c205a752a6a2cbe205ce243cf2612ac57614025050be17d'; need(producer.is_file() and sha(producer)==producer_pin,'XQ91 producer drift')
for name in ('ArithmeticAdaptiveMainOrientation2011','ArithmeticAdaptiveQuotients2011','ArithmeticAdaptiveFirstDivisibility2011'):
 need('DiophantineConsistency/'+name+'.olean' in before,'missing selected '+name)
initial=resource();need(initial['mem_available_kib']>=8*1024**2 and len(initial['lean'])<2,'resource guard')
OBS.mkdir(parents=True);out=Path(tempfile.mkdtemp(prefix='direct-main-projection-'));src=H/'DirectMainEarly.lean';copy=out/src.name;shutil.copyfile(src,copy);shutil.copyfile(src,OBS/'source.txt');sourcehash=sha(src);runnerhash=sha(H/'run-early.py');leanhash=sha(LEAN)
env={'PATH':'/usr/bin:/bin','LEAN_PATH':f'/tmp/direct-main-projection-c775ytrj:/tmp/direct-main-projection-u2r3kvhj:/tmp/direct-main-projection-s_f4nqkk:/tmp/direct-main-projection-ytn97sld:/tmp/direct-main-projection-dday1men:/tmp/direct-main-projection-zl1ey0e5:/tmp/direct-main-projection-wwbiv9_g:/tmp/direct-main-projection-d1lhwfdm:/tmp/direct-main-projection-f54kqb9e:/tmp/direct-main-projection-klvywrx4:/tmp/direct-main-projection-hxla92vq:/tmp/free-j-qcube92-ye71qcst:{LIB}:{PACKAGE}','LEAN_NUM_THREADS':'1'}
cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={out}',str(copy),'-o',str(out/'DirectMainEarly.olean')]
samples=[];start=time.monotonic();reason=None
with (out/'stdout').open('x') as so,(out/'stderr').open('x') as se:
 proc=subprocess.Popen(cmd,env=env,stdout=so,stderr=se,text=True)
 try:
  while proc.poll() is None:
   snap=resource();samples.append(snap)
   if snap['mem_available_kib']<8*1024**2 or len(snap['lean'])>2:reason='resource guard';break
   if time.monotonic()-start>180:reason='timeout';break
   time.sleep(2)
 except Exception as exc:reason='monitor error: '+repr(exc)
 finally:
  if reason and proc.poll() is None:proc.kill()
  proc.wait()
stdout=(out/'stdout').read_text();stderr=(out/'stderr').read_text();(OBS/'stdout').write_text(stdout);(OBS/'stderr').write_text(stderr);after=inventory(base);need(rank.is_file() and sha(rank)==rank_pin,'rank producer changed');need(indices.is_file() and sha(indices)==indices_pin,'indices producer changed');need(oriented.is_file() and sha(oriented)==oriented_pin,'oriented producer changed');need(pell.is_file() and sha(pell)==pell_pin,'pell producer changed');need(norm.is_file() and sha(norm)==norm_pin,'norm producer changed');need(projection.is_file() and sha(projection)==projection_pin,'projection producer changed');need(main.is_file() and sha(main)==main_pin,'main producer changed');need(transport.is_file() and sha(transport)==transport_pin,'transport producer changed');need(quotient.is_file() and sha(quotient)==quotient_pin,'quotient producer changed');need(first.is_file() and sha(first)==first_pin,'first producer changed');need(graph.is_file() and sha(graph)==graph_pin,'graph producer changed');need(producer.is_file() and sha(producer)==producer_pin,'XQ91 producer changed');obj=out/'DirectMainEarly.olean'
result={'command':cmd,'lean_path':env['LEAN_PATH'],'output_root':str(out),'exit':proc.returncode,'reason':reason,'elapsed':time.monotonic()-start,'source_sha256':sourcehash,'source_after':sha(src),'runner_sha256':runnerhash,'runner_after':sha(H/'run-early.py'),'lean_sha256':leanhash,'lean_after':sha(LEAN),'rank_producer_sha256':sha(rank),'indices_producer_sha256':sha(indices),'oriented_producer_sha256':sha(oriented),'pell_producer_sha256':sha(pell),'norm_producer_sha256':sha(norm),'projection_producer_sha256':sha(projection),'main_producer_sha256':sha(main),'transport_producer_sha256':sha(transport),'quotient_producer_sha256':sha(quotient),'first_producer_sha256':sha(first),'graph_producer_sha256':sha(graph),'xq91_producer_sha256':sha(producer),'base_receipt_sha256':sha(BASE),'union_count':len(before),'union_unchanged':before==after,'preflight':initial,'samples':samples,'object_sha256':sha(obj) if obj.is_file() else None,'stdout_sha256':sha(OBS/'stdout'),'stderr_sha256':sha(OBS/'stderr'),'scope':'Conditional model lemmas only; selected project provider, inherited package/dynamic/source-object ancestry.'}
(OBS/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({k:result[k] for k in ('exit','reason','elapsed','output_root','object_sha256','union_unchanged')}));print(stdout);print(stderr,file=sys.stderr)
need(proc.returncode==0 and not reason and obj.is_file() and before==after and sha(src)==sourcehash and sha(LEAN)==leanhash and sha(H/'run-early.py')==runnerhash and sha(BASE)==BASE_PIN and not any(t in stdout+stderr for t in ('error:','warning:','sorryAx')),'compile failed')
