#!/usr/bin/env python3
"""Guarded finite selector-list Lean check against selected BFS replay provider."""
from pathlib import Path
from hashlib import sha256
import json, os, re, subprocess, sys, tempfile, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
h=Path(__file__).resolve().parent;lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');lib=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');src=h/'BFSDisplayedLowInferredV2.lean';provider=Path('/tmp/bfs-printed-beta-sjarp8v0/BFSDisplayedBetaIPRAV2.olean');ipra=Path('/tmp/bfs-printed-ipra-9m_nfq32/BFSDisplayed80IPRA.olean');mask=lib/'DiophantineConsistency/CompactConcreteMask.olean';slots=Path('/tmp/bfs-printed-slots-qwdduxw9/BFSDisplayedSlots.olean');kernel=Path('/tmp/bfs-printed-kernel-orsko0l9/BFSDisplayedKernelV4.olean');endpoint=lib/'DirectBFS80FixedIPRA.olean';selectors=Path('/tmp/bfs-printed-selectors-4w6qxofm/BFSDisplayedSelectors.olean');prior=lib/'DirectBFSSymbolicKernel.olean';coeff=lib/'DiophantineConsistency/CompactCoefficientMass.olean';replay=h.parent/'direct-bfs-80-coherent-rebuild/observations/attempt01/result.json';pdf=h.parent/'ten-positive-80-bfs-decimal-display/equation.pdf'
pins={lean:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',src:'2603c327018a1f118341726746a674d90c1c46d7d433b4a345e497ec943b588d',provider:'b82dd329e8e0ac45932e9debd5ccae15b5c3133c1b9ce270891363a335624bd8',ipra:'db97c8d4717c6c0a70f51068c1c72b31e314d00864f5a56ac590e92a28367486',mask:'741c13117025cac74b3f94eb229f88f764aa101bf3cd9e4af3d4c0c43176cd0b',slots:'232a18c1544fa215d694391c3fa9fca75abb3eb1ae202f51c624d5a22147ee66',kernel:'bd6b509d78529c1c9879774a11989d605849c282ba4d408ef1ecfe1ed36bc072',endpoint:'2155f5f05a8e993dc3582f3c14ce9c56916d0ac09dc326c02093d83a878e4703',selectors:'92f60899906162de5e0ff953b4f9f0041f7471d17ee65e31a90db33b6363c65f',prior:'69f4a2f9d32229b6846ec7f0b84fe4b4d69d5eba8de1ff5c9ddb063e1d855c3f',coeff:'4a1745f314085517864a75307f4885f4eaf296ff983a91c0f2eca54f6386db9f',replay:'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559',pdf:'412ebf276d1e3d9b2802d333e020a4b7579f2368660bdede31be665564e40fe7'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def resources():
 ps=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in ps if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'lean':live,'mem_available_kib':mem}
for p,d in pins.items():need(sha(p)==d,'pin mismatch '+str(p))
need(re.findall(r'^import\s+(\S+)',src.read_text(),re.M)==['BFSDisplayedBetaIPRAV2'],'direct import mismatch')
a=os.environ.get('ATTEMPT','attempt01');need(re.fullmatch(r'attempt\d\d+',a),'attempt name');obs=h/'observations'/a;need(not os.path.lexists(obs),'observation exists');obs.mkdir(parents=True)
pre=resources();need(len(pre['lean'])<2 and pre['mem_available_kib']>=8*1024**2,'resource preflight')
out=Path(tempfile.mkdtemp(prefix='bfs-low-inferred-'));target=out/'BFSDisplayedLowInferredV2.olean';command=[str(lean),'-M3000','-j1','-DElab.async=false',str(src),'-o',str(target)];env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(provider.parent)+':'+str(ipra.parent)+':'+str(slots.parent)+':'+str(kernel.parent)+':'+str(selectors.parent)+':'+str(lib)+':'+str(pkg)};start=time.monotonic();samples=[];reason=None
with (obs/'stdout').open('x') as so,(obs/'stderr').open('x') as se:
 p=subprocess.Popen(command,env=env,stdout=so,stderr=se)
 while p.poll() is None:
  sample=resources();samples.append(sample)
  if len(sample['lean'])>2 or sample['mem_available_kib']<8*1024**2:reason='resource guard';p.terminate();break
  if time.monotonic()-start>300:reason='timeout';p.terminate();break
  time.sleep(2)
 try:p.wait(timeout=10)
 except subprocess.TimeoutExpired:p.kill();p.wait()
text=(obs/'stdout').read_text()+(obs/'stderr').read_text();ok=p.returncode==0 and reason is None and target.is_file() and not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',text)
pat=r"'BFSDisplayedLowInferred.low_formula' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
matches=re.findall(pat,text,re.S);ok=ok and len(matches)==1 and set(x.strip() for x in matches[0].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
for path,d in pins.items():need(sha(path)==d,'pin changed during run '+str(path))
record={'status':'PASS' if ok else 'FAILED','command':command,'exit':p.returncode,'reason':reason,'elapsed':time.monotonic()-start,'source_sha256':sha(src),'runner_sha256':sha(Path(__file__)),'pins':{str(k):{'sha256':v,'resolved':str(k.resolve())} for k,v in pins.items()},'output':str(target),'output_sha256':sha(target) if target.is_file() else None,'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),'preflight':pre,'samples':samples,'postflight':resources(),'scope':'selected-provider iPRA derivability with displayed beta and kernel; PDF extraction and inherited source/package/dynamic ancestry are external'}
(obs/'terminal.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':record['status'],'exit':record['exit'],'output':record['output'],'output_sha256':record['output_sha256']}));raise SystemExit(0 if ok else 1)
