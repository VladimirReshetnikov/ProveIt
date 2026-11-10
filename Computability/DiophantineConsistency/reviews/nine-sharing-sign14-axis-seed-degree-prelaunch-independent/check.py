#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-axis-seed-degree-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='9782bac6013dcd255c3946a0a6c36713f0c766041bcdfff687fba7649572cd8d' and sha(p/'source-manifest.json')=='9e9bf7ff721090216fc060fc1da0ee6e8ffd49c08ba7707cabcdca3df216fe9d'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];names=['Sign14AxisOtherDegree','Sign14AxisNoncancel','Sign14AxisSeedDegree'];assert [e['module'].split('.')[-1] for e in rows]==names;srcs=[]
for i,e in enumerate(rows):
 src=p/'src/DiophantineConsistency'/(names[i]+'.lean');s=src.read_text();srcs.append(s);assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']==['DiophantineConsistency.'+('Sign14AxisNaBinding' if i==0 else names[i-1])] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',s)
a,b,c=srcs;assert '[row00 p, row01 p, row02 p, row04 p]' in a and all('row'+f'{i:02}'+'_degree p' in a for i in (0,1,2,4)) and 'degree e ≤ 46' in a and 'natDegree ≤ 46' in a
assert all(t in b for t in ('other_sum_degree_le','natDegree ≤ 92','na_square_degree','natDegree = 124','combined_degree','row03_axis_degree p hz'))
assert all(t in c for t in ('theorem seed_axis','theorem seed_axis_degree','(hz : p 0 ≠ 0)','natDegree = 124','row03 p','otherSum p','combined_degree p hz'))
staged=(root/'research/nine-sharing-sign14-staged-syntax-check/src/DiophantineConsistency/SharingSeed14Degree124.lean').read_text();assert 'def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 15) := row00 p' in staged and '[row01 p, row02 p, row03 p, row04 p]' in staged and 'firstResidual p * firstResidual p' in staged
check=root/'reviews/nine-sharing-sign14-axis-na-binding-terminal-independent/check.py';assert sha(check)=='e1142d404fe504a1d2eeac70ef9939bc2f0f200e0f7c4d3970315e898827f7ea';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':3,'scope':'actual seed axis degree 124 under p0 nonzero; multivariate lower and external binding separate'},indent=2))
