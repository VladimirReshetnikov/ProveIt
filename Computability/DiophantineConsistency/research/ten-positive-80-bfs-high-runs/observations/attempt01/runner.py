#!/usr/bin/env python3
"""Guarded finite selector-list Lean check against selected BFS replay provider."""
from pathlib import Path
from hashlib import sha256
import json, os, re, subprocess, sys, tempfile, time
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
h=Path(__file__).resolve().parent;lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');lib=Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib');pkg=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');src=h/'BFSHighRuns.lean';provider=Path('/tmp/bfs-high-generic-nsp2g8fz/BFSHighGeneric.olean');mask=lib/'DiophantineConsistency/CompactConcreteMask.olean';high=lib/'DiophantineConsistency/CompactHighPopulation.olean';coeff=lib/'DiophantineConsistency/CompactCoefficientMass.olean';replay=h.parent/'direct-bfs-80-coherent-rebuild/observations/attempt01/result.json';pdf=h.parent/'ten-positive-80-bfs-decimal-display/equation.pdf'
pins={lean:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',src:'3958f48a99292c04d1353d65852e5bcdd13137aab46e393aadcb63d07cfa0efb',mask:'741c13117025cac74b3f94eb229f88f764aa101bf3cd9e4af3d4c0c43176cd0b',high:'65e9dee3cd5b9a91f396ece5e2bcc3ad34a5f50670f5e75629ae02f85dccbd8a',provider:'cdb9593b8e095fbe92ecc3d89fef9e7c77c4a98a3b1688b4988d6d48bc7cc1ff',coeff:'4a1745f314085517864a75307f4885f4eaf296ff983a91c0f2eca54f6386db9f',replay:'ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559',pdf:'412ebf276d1e3d9b2802d333e020a4b7579f2368660bdede31be665564e40fe7'}
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
def resources():
 ps=subprocess.run(['ps','-eo','pid=,comm=,rss=,args='],capture_output=True,text=True,check=True).stdout.splitlines();live=[x.strip() for x in ps if len(x.split(None,3))==4 and x.split(None,3)[1]=='lean'];mem=int(next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')).split()[1]);return {'time_ns':time.time_ns(),'lean':live,'mem_available_kib':mem}
for p,d in pins.items():need(sha(p)==d,'pin mismatch '+str(p))
need(re.findall(r'^import\s+(\S+)',src.read_text(),re.M)==['BFSHighGeneric'],'direct import mismatch')
a=os.environ.get('ATTEMPT','attempt01');need(re.fullmatch(r'attempt\d\d+',a),'attempt name');obs=h/'observations'/a;need(not os.path.lexists(obs),'observation exists');obs.mkdir(parents=True)
pre=resources();need(len(pre['lean'])<2 and pre['mem_available_kib']>=8*1024**2,'resource preflight')
out=Path(tempfile.mkdtemp(prefix='bfs-high-runs-'));target=out/'BFSHighRuns.olean';command=[str(lean),'-M3000','-j1','-DElab.async=false',str(src),'-o',str(target)];env={'PATH':'/usr/bin:/bin','LEAN_PATH':str(provider.parent)+':'+str(lib)+':'+str(pkg)};start=time.monotonic();samples=[];reason=None
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
pat=r"'BFSHighRuns.expansion' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)"
matches=re.findall(pat,text,re.S);ok=ok and len(matches)==1 and set(x.strip() for x in matches[0].split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
for path,d in pins.items():need(sha(path)==d,'pin changed during run '+str(path))
record={'status':'PASS' if ok else 'FAILED','command':command,'exit':p.returncode,'reason':reason,'elapsed':time.monotonic()-start,'source_sha256':sha(src),'runner_sha256':sha(Path(__file__)),'pins':{str(k):{'sha256':v,'resolved':str(k.resolve())} for k,v in pins.items()},'output':str(target),'output_sha256':sha(target) if target.is_file() else None,'stdout_sha256':sha(obs/'stdout'),'stderr_sha256':sha(obs/'stderr'),'preflight':pre,'samples':samples,'postflight':resources(),'scope':'selected-provider generic low mask identity; PDF extraction and inherited source/package/dynamic ancestry are external'}
(obs/'terminal.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':record['status'],'exit':record['exit'],'output':record['output'],'output_sha256':record['output_sha256']}));raise SystemExit(0 if ok else 1)
