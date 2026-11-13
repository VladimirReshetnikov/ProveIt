from pathlib import Path
from collections import defaultdict,deque
import hashlib,json,os,re,subprocess,sys
root=Path(__file__).resolve().parents[2];h=root/'research/trace75-baseline-four-provenance';a=h/'observations/attempt02';oldroot=root/'research/ten-positive-80-coherent-rebuild/observations/attempt04';oo=root/'research/ten-positive-80-coherent-rebuild/observations/outer-attempt04';finalroot=root/'research/trace75-bfs-ipra-final-assembly-plan/observations/attempt01';bfsfile=root/'research/direct-bfs-80-coherent-rebuild/observations/attempt01/initial-project.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(h/'check.py')=='bc386cc00dbd55472b1e304792333fea7de6ee976db472144de4e03a0fa5f528' and sha(a/'terminal.json')=='4a63b4c3cb7938ff3c6f49001f273a1a03d735d06c547a170bf8fd99c6c9540e' and sha(a/'stdout')=='72587a664b8d7a41704b146ad054c33bf1cdc70b9ae891fca18b11e9425a51b7'
terminal=json.loads((a/'terminal.json').read_text());assert terminal['exit']==0 and sha(a/'stdout')==terminal['stdout_sha256'] and sha(a/'stderr')==terminal['stderr_sha256'] and not (a/'stderr').read_bytes()
r=subprocess.run([sys.executable,'-I','-S','-B',str(h/'check.py')],capture_output=True,text=True);assert r.returncode==0 and r.stdout==(a/'stdout').read_text() and not r.stderr
old=json.loads((oldroot/'result.json').read_text());outer=json.loads((oo/'terminal.json').read_text());final=json.loads((finalroot/'result.json').read_text());bfs=json.loads(bfsfile.read_text());obs=json.loads((a/'stdout').read_text());assert old['status']=='PASS' and len(old['stages'])==127 and outer['exit']==0 and outer['runner_sha256_before']==outer['runner_sha256_after']==sha(root/'research/ten-positive-80-coherent-rebuild/run-v6.py')
names={'DiophantineConsistency.ModelArithmetic':5,'DiophantineConsistency.ModelExponentialCongruence':9,'PellOddFold':45,'PellRecovery':46};stages={s['module']:s for s in old['stages']};assert {x['module']:x['stage'] for x in obs['records']}==names
def hashes(bundle):return {n:(None if x is None else x['sha256']) for n,x in bundle.items()}
def current(bundle):
 stem=str(bundle['.olean']['path'])[:-6]
 for suffix,item in bundle.items():
  p=Path(stem+suffix)
  if item is None:assert not os.path.lexists(p),(stem,suffix)
  else:assert p.is_file() and str(p.resolve(strict=True))==item['resolved'] and sha(p)==item['sha256'],p
for n,index in names.items():
 s=stages[n];assert s['index']==index and s['exit']==0 and s['reason'] is None and s['direct_before']==s['direct_after'];source=Path(s['command'][5]);assert sha(source)==s['source_sha256']
 out=s['output'];selected=final['selected_project'][n];initial=bfs[n];assert hashes(out)==hashes(selected)==hashes(initial) and os.path.samefile(out['.olean']['path'],selected['.olean']['path']) and not Path(out['.olean']['path']).is_symlink()
 for b in (out,selected,initial):current(b)
 assert old['headers'][n]==final['serialized_headers'][n] and [x for x in old['headers'][n] if x!='Init']==re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',source.read_text(),re.M) and set(old['headers'][n])==set(s['direct_before'])
 for dep,producer in s['direct_before'].items():
  chosen=final['selected_project'].get(dep) or final['selected_outside'].get(dep);assert chosen is not None and hashes(producer)==hashes(chosen);current(producer);current(chosen)
 print(n,'producer stage',index,'direct imports',len(s['direct_before']),'sha',out['.olean']['sha256'])
project=set(final['closures']['Trace75BFSFixedIPRA']['project']);headers=final['serialized_headers'];assert len(project)==1868;reverse=defaultdict(set)
for module in project:
 for dep in headers[module]:
  if dep in project:reverse[dep].add(module)
def down(seeds):
 seen=set(seeds);todo=deque(seeds)
 while todo:
  for n in reverse[todo.popleft()]:
   if n not in seen:seen.add(n);todo.append(n)
 return sorted(seen)
assert down(names)==obs['reverse_reachable'] and len(down(names))==obs['reverse_reachable_count']==186
assert {n:len(down([n])) for n in names}==obs['per_seed_counts'];print('PASS direct producer capture, current runner pin and 186-node reverse reachability; no Lean replay')
