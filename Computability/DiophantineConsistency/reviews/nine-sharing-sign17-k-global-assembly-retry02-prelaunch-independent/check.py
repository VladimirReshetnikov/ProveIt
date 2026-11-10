#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-global-assembly-retry02-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='32ff381103a10e321922b2860e997afbd67d052dff4b39d83bc980677a7dc534' and sha(p/'source-manifest.json')=='db11f0517267e4fbde5446e5532e7021634c78aa33586c9b45e0814cbe5025df'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==5;rank=json.loads((root/'research/nine-sharing-sign17-k-global-rank-check/source-manifest.json').read_text())['rows'];assert rows[:4]==rank
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
e=rows[-1];assert e['module']=='DiophantineConsistency.Sign17KGlobalAssembly' and e['imports']==['DiophantineConsistency.Sign17KGlobalRankConditional']+[f'DiophantineConsistency.Sign17KGlobalChunk{i:02}' for i in range(15)];s=(p/'src/DiophantineConsistency/Sign17KGlobalAssembly.lean').read_text()
old=(root/'research/nine-sharing-sign17-k-global-assembly-retry-check/src/DiophantineConsistency/Sign17KGlobalAssembly.lean').read_text()
for kind in ('nonzero','adjacent'):
 a=f'Sign17KGlobalChunk00.{kind}Index, Fin.natAdd, Fin.castAdd, Fin.castLE, Fin.castLE_mk';b=f'Sign17KGlobalChunk00.{kind}Index, Fin.natAdd, Fin.castAdd, Fin.castLE_mk';assert s.count(a)==1;old=old.replace(b,a)
assert old==s
parts=s.split('theorem numeric_adjacent');assert len(parts)==2
for t,total,which in [(parts[0],941,'nonzero'),(parts[1].split('theorem global_nonzero')[0],940,'adjacent')]:
 cases=[int(x) for x in re.findall(r'Fin.addCases \(m := 64\) \(n := (\d+)\)',t)];assert cases==[total-64*(i+1) for i in range(14)]
 used=re.findall(r'using Sign17KGlobalChunk(\d\d)\.'+which+r' (x\d+|j\d+)',t);assert used==[(f'{i:02}',f'x{i}') for i in range(14)]+[('14','j13')]
 assert [int(x) for x in re.findall(r'Sign17KGlobalChunk(\d\d)\.'+which+'Index',t)]==list(range(15))
for t in ('theorem tail_nonzero : ∀ i : Fin 941','theorem numeric_adjacent : ∀ i : Fin 940','theorem global_nonzero : ∀ i, i ≠ 0 →','| zero => exact False.elim (hi rfl)','| succ i => exact tail_nonzero i','theorem candidate_positions : ∀ i, MF.WangTiles942.physicalMap (Sign17KWeightUnion942.indices i) = i','Sign17KGlobalRankConditional.candidate_positions_if','Sign17KGlobalChunk00.start_index global_nonzero numeric_adjacent'):assert t in s
for f in ('nine-sharing-sign17-k-weight-union942-terminal-independent','nine-sharing-sign17-k-global-chunks-terminal-independent','nine-sharing-sign17-k-global-rank-terminal-independent','nine-sharing-sign17-k-partition-probe-retry-terminal-independent','nine-sharing-sign17-k-global-assembly-terminal-independent','nine-sharing-sign17-k-global-assembly-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and "elif depname in chunk_names:path=CHUNKS/" in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':5,'chunks':15,'nonzero_cases':941,'adjacent_cases':940,'scope':'proposed unconditional physical positions of in-Lean candidate; no K/file/JSON theorem'},indent=2))
