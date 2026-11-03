#!/usr/bin/env python3
"""Bounded check of the generic 79 gauge algebra."""
from pathlib import Path
from hashlib import sha256
import json,os,re,subprocess,sys,tempfile,time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
h=Path(__file__).resolve().parent;lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');src=h/'Mask79ModelBridgeV2.lean';foundation=pkg/'Foundation/FirstOrder/Arithmetic/IOpen/Basic.olean';provider=Path('/tmp/mask79-output-cqfif459/Mask79ActualOutput.olean');actual=Path('/tmp/mask79-actual-f441d356/Mask79ActualRowsV3.olean');model=Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ModelDifferenceRing.olean');rows=Path('/tmp/mask79-ring-92upnp8s/MaskCoordinate79.olean');carrier=Path('/tmp/mask79-carrier-w290b5ah/Mask79Carrier.olean');graph=Path('/tmp/tenpositive-80graph-d2v79zbc/Direct80Graph.olean');mathlib=pkg/'Mathlib/Tactic/Ring.olean'
pins={lean:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',src:'67ad34d1088d778ad49cb2c473c17f8e2fa3c076d9ec6195afb9b4e0a66c8b83',foundation:'fdf05f04ff241ddea16128e1fc799cc5cc9470fbc1a63c92a200688ee597ef45',provider:'74ff4836864800cfd4c6720c005ec7263038ac79b814576c8885ea706c8e703a',actual:'99cb4d4e542ccef9de028afdd36b2d283c50129c48159a7454198a098cc31151',model:'d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74',rows:'7fac254b7efc456af7f4aa03ac2d1fa80c23c18faac88ccfd46914b3d07184f6',carrier:'a880a3df700be3af796282b0600161756e640ad7da78fdcb383fa49b1c2f5b60',graph:'95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4',mathlib:'cc12dfa66db7ef6ae4cd2d7a4e035ddffaca827168243f728812776b77836eb4'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def resources():
 ps=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in ps if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'lean':live,'mem_available_kib':mem}
for p,d in pins.items():need(sha(p)==d,'pin mismatch '+str(p))
need(re.findall(r'^import\s+(\S+)',src.read_text(),re.M)==['Mask79ActualOutput','DiophantineConsistency.ModelDifferenceRing','Foundation.FirstOrder.Arithmetic.IOpen.Basic'],'direct import mismatch')
a=os.environ.get('ATTEMPT','attempt01');need(re.fullmatch(r'attempt\d\d+',a),'attempt name');obs=h/'observations'/a;need(not os.path.lexists(obs),'observation exists');obs.mkdir(parents=True)
pre=resources();need(len(pre['lean'])<2 and pre['mem_available_kib']>=8*1024**2,'resource preflight')
out=Path(tempfile.mkdtemp(prefix='mask79-modelbridge-'));target=out/'Mask79ModelBridgeV2.olean';command=[str(lean),'-M3000','-j1','-DElab.async=false',str(src),'-o',str(target)];env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(provider.parent)+':'+str(actual.parent)+':'+str(rows.parent)+':'+str(carrier.parent)+':'+str(graph.parent)+':/tmp/direct90-ipra-join-b66u_qqo/lib:'+str(pkg)};start=time.monotonic();samples=[];reason=None
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
pat=r"'Mask79ModelBridge.zero_preserved_of_lift' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)";matches=re.findall(pat,text,re.S);ok=ok and len(matches)==1 and set(x.strip() for x in matches[0].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
for path,d in pins.items():need(sha(path)==d,'pin changed during run '+str(path))
record={'status':'PASS' if ok else 'FAILED','command':command,'exit':p.returncode,'reason':reason,'elapsed':time.monotonic()-start,'source_sha256':sha(src),'runner_sha256':sha(Path(__file__)),'pins':{str(k):{'sha256':v,'resolved':str(k.resolve())} for k,v in pins.items()},'output':str(target),'output_sha256':sha(target) if target.is_file() else None,'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),'preflight':pre,'samples':samples,'postflight':resources(),'scope':'conditional model-zero bridge; cast matching and positivity remain explicit'}
(obs/'terminal.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':record['status'],'exit':record['exit'],'output':record['output'],'output_sha256':record['output_sha256']}));raise SystemExit(0 if ok else 1)
