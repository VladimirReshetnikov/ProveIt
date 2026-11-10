#!/usr/bin/env python3
import ast,hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-lines-target-order-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='fef37b4b100dfe67d88b897fc97ce91b0eafe3fea1c81e275c5cda4fcb01eb43' and sha(p/'source-manifest.json')=='e59083941a9a6fecf5f3d8d884830bef80f510f85c0cd3fa29d86ab112ebe781'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign17LinesTargetOrder';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign17LinesRails'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='f60e0ebc959f41227a06a5ad5fb83e532d6a2f0d222eaaed8f7d68a2c9896159' and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for z in ('(WangTiles942.targetsFrom d lineActions).sort (· ≤ ·)','(WangTiles942.targetList d).Pairwise (· ≤ ·)','WangTiles942.targetList d = lineTargetList d','← target_set_from_lines','WangTiles942.targetList_nodup d','List.toFinset_sort'):assert z in s
old=(root/'Lean/DiophantineConsistency/WangTiles942Data.lean').read_text();m=re.search(r'def targetList \(d : Bool\).*?if d then (\[[^\]]*\]) else (\[[^\]]*\])',old,re.S);assert m;lists=[ast.literal_eval(m.group(i)) for i in (1,2)];assert all(xs==sorted(set(xs)) for xs in lists) and 'def targets (d : Bool) : Finset ℕ := (targetList d).toFinset' in old
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-lines-rails-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','target_list_lengths':[len(x) for x in lists],'scope':'proposed sorted target-list equality only; full table/PDF/file separate'},indent=2))
