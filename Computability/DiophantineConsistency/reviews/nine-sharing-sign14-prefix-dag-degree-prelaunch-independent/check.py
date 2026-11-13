#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-dag-degree-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='2bc017b2955e2aa2532df8d56c7992d7ad2b937263901deaeb3db1df41e106aa' and sha(p/'source-manifest.json')=='5e6e5eddf20fb0562d5634b91cb2dc18bea16dd780296736c60aa7c12883c22a'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14PrefixDagDegree.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14PrefixDagDegree' and e['imports']==['DiophantineConsistency.Sign14PrefixDagAssembly','DiophantineConsistency.Sign14ExactDegree'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('Sign14PrefixDagAssembly.expression CurrentWindowCarry2011.ports','expression = Sign14CurrentExpression.expression','Sign14PrefixDagAssembly.expression_eq CurrentWindowCarry2011.ports','expression.toPolynomial.totalDegree = 124','rw [expression_eq]','Sign14ExactDegree.current_exact'):assert t in s
for f in ('nine-sharing-sign14-prefix-dag-assembly-terminal-independent','nine-sharing-sign14-exact-degree-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider-survey.py')],capture_output=True,text=True,check=True,timeout=180);v=json.loads(x.stdout);assert not x.stderr and v['status']=='PASS' and v['overlap_count']==1075 and len(v['extra'])==69
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','overlaps':1075,'extra':69,'scope':'degree 124 of current embedded-DAG symbolic expression conditional on Lean; external original-file/JSON/PDF relation separate'},indent=2))
