#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-control-block-sum-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='0a43fc37a0dacd5b1fd26c86acb64b4fc3717083f40b91b8571a32e66c5a651f' and sha(p/'source-manifest.json')=='6a781ae8d11840d03678b86bcaa04d9f0d1ad5f93a82e1b0f0e71d663b0cec2e'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==3
for i,e in enumerate(rows):
 n=e['module'].split('.')[-1];q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 if i<2:
  stem=['nine-sharing-sign17-k-control-blocks-check','nine-sharing-sign17-k-control-append-check'][i];state=json.loads((root/'research'/stem/'attempt01/state.json').read_text());assert state['status']=='PASS' and state['rows'][0]['source_sha256']==e['source_sha256']
assert rows[-1]['imports']==['DiophantineConsistency.Sign17KControlAppend','DiophantineConsistency.Sign17KControlBlocks'];s=(p/'src/DiophantineConsistency/Sign17KControlBlockSum.lean').read_text()
for t in ('theorem symbolic_sum (r : ℕ)','∑ i : Fin 44, symbolic i * r ^ (1005 - (942 + i.val))','Sign17KRankedRawWord.controls r','Sign17KControlAppend.append_power_sum','theorem literal_sum_eq (r : ℕ)','∑ i : Fin 44, literal i * r ^ (1005 - (942 + i.val))','theorem controls_as_sum (r : ℕ)','rw [literal_sum_eq, symbolic_sum]'):assert t in s
sizes=[9,9,9,8,1,8];offset=942;offsets=[]
for x in sizes:offsets.append(offset);offset+=x
assert offsets==[942,951,960,969,977,978] and offset==986
for f in ('nine-sharing-sign17-k-control-blocks-terminal-independent','nine-sharing-sign17-k-control-append-terminal-independent','nine-sharing-sign17-k-ranked-rawword-retry-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':3,'block_offsets':offsets,'scope':'symbolic/literal control sum transfer; full K/external file separate'},indent=2))
