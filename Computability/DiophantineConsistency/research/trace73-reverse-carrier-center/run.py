#!/usr/bin/env python3
"""Bounded check of the generic 79 gauge algebra."""
from pathlib import Path
from hashlib import sha256
import json,os,re,subprocess,sys,tempfile,time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
h=Path(__file__).resolve().parent;lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');src=h/'Trace73ReverseCenter.lean';provider=Path('/tmp/trace75-provider-wljjm6ws/DiophantineConsistency/TenPositiveTrace75.olean');candidate=h.parent/'trace73-center-probe/candidate.json';parent=h.parents[1]/'Lean/DiophantineConsistency/TenPositiveTrace75.lean'
pins={Path('/tmp/reverse-carrier-fr1w8a_6/ReverseCarrier.olean'):'614ce881139dbf86b9080fa156e87f2c84d0b19eceabc522b008f44b8c9ebbaa',Path('/tmp/trace-centerpositive-0_fb28_g/TraceCenterPositiveV2.olean'):'c1502792816d437971e4fa1fc632a3d78fbaafe89a15925820b11a136c29799e',lean:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',Path('/tmp/trace73-literal-1adlrevr/Trace73Literal.olean'):'e4bbe335d32f1f50ed2bfe2440c37f19a1f34ae4def4ff476b6e0778dfc3654d',Path('/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ModelDifferenceRing.olean'):'d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74',pkg/'Foundation/FirstOrder/Arithmetic/IOpen/Basic.olean':'fdf05f04ff241ddea16128e1fc799cc5cc9470fbc1a63c92a200688ee597ef45',Path('/tmp/trace73-center-r4z617bq/Trace73CenterV2.olean'):'fe3d39ec315888286a4d9d5ec2763badf338dc11bf141c0e19fa58f575de1e5a',src:'aca8db2b513927a54b9168384a92cb25c7c99260b72d6948d3d031c9eae51c56',provider:'1ae82441c7023e9675c5cc532d4026da6a3ee77e906996d67c315e4f693b079c',parent:'0df718ab69ae7aef32dd341ee355ea2e21214e97fbea225af8816519fe383db9',candidate:'c83151606214c211993fa0c5b9913abae3b6bcf2b00af107e599e4855f936ca6'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def resources():
 ps=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in ps if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'lean':live,'mem_available_kib':mem}
for p,d in pins.items():need(sha(p)==d,'pin mismatch '+str(p))
need(re.findall(r'^import\s+(\S+)',src.read_text(),re.M)==['ReverseCarrier','TraceCenterPositiveV2'],'direct import mismatch')
a=os.environ.get('ATTEMPT','attempt01');need(re.fullmatch(r'attempt\d\d+',a),'attempt name');obs=h/'observations'/a;need(not os.path.lexists(obs),'observation exists');obs.mkdir(parents=True)
pre=resources();need(len(pre['lean'])<2 and pre['mem_available_kib']>=8*1024**2,'resource preflight')
out=Path(tempfile.mkdtemp(prefix='trace73-reverse-'));union=out/'union';base=Path('/tmp/direct90-ipra-join-b66u_qqo/lib');
for root,dirs,files in os.walk(base,followlinks=True):
 for file in files:
  orig=Path(root)/file;dest=union/orig.relative_to(base);dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(orig.resolve())
obj=union/'DiophantineConsistency/TenPositiveTrace75.olean';obj.unlink(missing_ok=True);obj.symlink_to(provider.resolve());target=out/'Trace73ReverseCenter.olean';command=[str(lean),'-M3000','-j1','-DElab.async=false',str(src),'-o',str(target)];env={'PATH':'/usr/bin:/bin','LEAN_PATH':'/tmp/reverse-carrier-fr1w8a_6:/tmp/trace-centerpositive-0_fb28_g:'+str(union)+':'+str(pkg)};start=time.monotonic();samples=[];reason=None
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
for name in ('positive_carrier_center',):
 pat=r"'Trace73ReverseCenter\."+re.escape(name)+r"' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
 matches=re.findall(pat,text,re.S);ok=ok and len(matches)==1 and set(x.strip() for x in matches[0].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
for path,d in pins.items():need(sha(path)==d,'pin changed during run '+str(path))
record={'status':'PASS' if ok else 'FAILED','command':command,'exit':p.returncode,'reason':reason,'elapsed':time.monotonic()-start,'source_sha256':sha(src),'runner_sha256':sha(Path(__file__)),'pins':{str(k):{'sha256':v,'resolved':str(k.resolve())} for k,v in pins.items()},'output':str(target),'output_sha256':sha(target) if target.is_file() else None,'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),'preflight':pre,'samples':samples,'postflight':resources(),'scope':'conditional positive-model witness transfer; center and shift witnesses remain assumptions'}
(obs/'terminal.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':record['status'],'exit':record['exit'],'output':record['output'],'output_sha256':record['output_sha256']}));raise SystemExit(0 if ok else 1)
