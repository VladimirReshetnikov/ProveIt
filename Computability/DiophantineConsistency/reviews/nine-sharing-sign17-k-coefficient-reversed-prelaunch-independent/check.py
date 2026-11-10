#!/usr/bin/env python3
import ast,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-coefficient-reversed-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='45916da0f7a6da20f89d172c1f245c8dfae83572874754f25f8d25ac3ace9f36' and sha(p/'source-manifest.json')=='ac384f628018b388f7ba0745a809001767e8161972b2d36efaf80072ca78ab71' and sha(root/'research/nine-sharing-sign17-k-coefficient-reversed-draft/generate.py')=='df7a79e3fd55a24c29f123eb8002bb0db69846a94de27eddfe65a7700a958f66'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==8;seen={}
for i,e in enumerate(rows):
 n=f'Sign17KCoefficientReversed{i:02}';pn=f'Sign17KCoefficientLists{i:02}';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.'+pn] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 src=(root/'research/nine-sharing-sign17-k-coefficient-lists-check/src/DiophantineConsistency'/(pn+'.lean')).read_text();names=[f'block{j:02}' for j in (2*i,2*i+1)]+(['control'] if i==0 else [])
 for name in names:
  m=re.search(r'theorem '+name+r'\s*:\s*List\.ofFn ([A-Za-z0-9_.]+) = (\[[^\]]*\])',src);assert m
  z=re.search(r'theorem '+name+r'\s*:\s*\(List\.ofFn ([A-Za-z0-9_.]+)\)\.reverse = (\[[^\]]*\]) := by\s*rw \['+pn+r'\.'+name+r'\]\s*decide \+kernel',s);assert z and m.group(1)==z.group(1) and ast.literal_eval(m.group(2))[::-1]==ast.literal_eval(z.group(2));seen[name]=len(ast.literal_eval(z.group(2)))
 assert s.count('#print axioms ')==len(names)
assert len(seen)==17 and sum(v for k,v in seen.items() if k!='control')==942 and seen['control']==44
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-coefficient-lists-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
prior=json.loads((root/'research/nine-sharing-sign17-k-coefficient-lists-check/attempt01/state.json').read_text());assert prior['status']=='PASS' and len(prior['rows'])==8
for row in prior['rows']:assert sha(Path('/tmp/nine-sharing-sign17-k-coefficient-lists-20261110/lib/DiophantineConsistency')/(row['module']+'.olean'))==row['object_sha256']
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':8,'tile_entries':942,'control_entries':44,'scope':'17 in-Lean list reversals only; full stream/fixture and file linkage separate'},indent=2))
