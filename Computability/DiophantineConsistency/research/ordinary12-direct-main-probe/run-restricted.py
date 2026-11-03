#!/usr/bin/env python3
"""Bounded author check of conditional direct-main lemmas on the 92 provider."""
from pathlib import Path
from hashlib import sha256
import json,os,shutil,subprocess,sys,tempfile,time
if sys.flags.optimize:raise SystemExit('optimized Python refused')
H=Path(__file__).resolve().parent;D=H.parents[1];a=os.environ.get('ATTEMPT','attempt01')
if not a.startswith('attempt') or not a[7:].isdigit():raise SystemExit('invalid attempt')
OBS=H/'observations'/('restricted-'+a)
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
forward=Path('/tmp/direct-main-projection-vpzhjdgc/DirectMainForward.olean'); forward_pin='46ace173cb7c23931d94b46fbf829ae86b69e16242d6ca88363000151be7e8fd'; need(forward.is_file() and sha(forward)==forward_pin,'forward producer drift')
graph=Path('/tmp/direct-main-projection-hxla92vq/DirectMainGraph.olean'); graph_pin='fc4e4c2f55ead02cd216f1225933650e9ecfec11251a76def53f886380ec3f31'; need(graph.is_file() and sha(graph)==graph_pin,'graph producer drift')
producer=Path('/tmp/free-j-qcube92-ye71qcst/XQ91.olean'); producer_pin='747df97728f8c8125c205a752a6a2cbe205ce243cf2612ac57614025050be17d'; need(producer.is_file() and sha(producer)==producer_pin,'XQ91 producer drift')
for name in ('ArithmeticAdaptiveMainOrientation2011','ArithmeticAdaptiveQuotients2011','ArithmeticAdaptiveFirstDivisibility2011'):
 need('DiophantineConsistency/'+name+'.olean' in before,'missing selected '+name)
initial=resource();need(initial['mem_available_kib']>=8*1024**2 and len(initial['lean'])<2,'resource guard')
OBS.mkdir(parents=True);out=Path(tempfile.mkdtemp(prefix='direct-main-projection-'));src=H/'DirectMainRestricted.lean';copy=out/src.name;shutil.copyfile(src,copy);shutil.copyfile(src,OBS/'source.txt');sourcehash=sha(src);runnerhash=sha(H/'run-restricted.py');leanhash=sha(LEAN)
env={'PATH':'/usr/bin:/bin','LEAN_PATH':f'/tmp/direct-main-projection-vpzhjdgc:/tmp/direct-main-projection-hxla92vq:/tmp/free-j-qcube92-ye71qcst:{LIB}:{PACKAGE}','LEAN_NUM_THREADS':'1'}
cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false',f'--root={out}',str(copy),'-o',str(out/'DirectMainRestricted.olean')]
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
stdout=(out/'stdout').read_text();stderr=(out/'stderr').read_text();(OBS/'stdout').write_text(stdout);(OBS/'stderr').write_text(stderr);after=inventory(base);need(forward.is_file() and sha(forward)==forward_pin,'forward producer changed');need(graph.is_file() and sha(graph)==graph_pin,'graph producer changed');need(producer.is_file() and sha(producer)==producer_pin,'XQ91 producer changed');obj=out/'DirectMainRestricted.olean'
result={'command':cmd,'lean_path':env['LEAN_PATH'],'output_root':str(out),'exit':proc.returncode,'reason':reason,'elapsed':time.monotonic()-start,'source_sha256':sourcehash,'source_after':sha(src),'runner_sha256':runnerhash,'runner_after':sha(H/'run-restricted.py'),'lean_sha256':leanhash,'lean_after':sha(LEAN),'forward_producer_sha256':sha(forward),'graph_producer_sha256':sha(graph),'xq91_producer_sha256':sha(producer),'base_receipt_sha256':sha(BASE),'union_count':len(before),'union_unchanged':before==after,'preflight':initial,'samples':samples,'object_sha256':sha(obj) if obj.is_file() else None,'stdout_sha256':sha(OBS/'stdout'),'stderr_sha256':sha(OBS/'stderr'),'scope':'Conditional model lemmas only; selected project provider, inherited package/dynamic/source-object ancestry.'}
(OBS/'terminal.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({k:result[k] for k in ('exit','reason','elapsed','output_root','object_sha256','union_unchanged')}));print(stdout);print(stderr,file=sys.stderr)
need(proc.returncode==0 and not reason and obj.is_file() and before==after and sha(src)==sourcehash and sha(LEAN)==leanhash and sha(H/'run-restricted.py')==runnerhash and sha(BASE)==BASE_PIN and not any(t in stdout+stderr for t in ('error:','warning:','sorryAx')),'compile failed')
