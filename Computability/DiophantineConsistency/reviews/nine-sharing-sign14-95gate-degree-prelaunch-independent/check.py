#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-95gate-degree-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='85d46dc3e79175adcfb55b335aad7115e85f6fc12da629a7854c2c62c88940b2' and sha(p/'provider-survey.py')=='34bcdbb9a3f9c9c3d2730d5234b77b097fdc93fc2b71dd4a5478aa7feee165b6' and sha(p/'source-manifest.json')=='39b7be81d8ef76dfa3fa547834f966881bd2c10205c7f88302a39c8cfb6a8622'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized95Degree.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized95Degree' and e['imports']==['DiophantineConsistency.Sign14Optimized95Expression','DiophantineConsistency.Sign14ExactDegree'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('Sign14Optimized95Expression.expression CurrentWindowCarry2011.ports','expression.toPolynomial.totalDegree = 124','Sign14Optimized95Expression.polynomial_eq','Sign14ExactDegree.current_exact'):assert t in s
for f in ('nine-sharing-sign14-prefix-dag-degree-terminal-independent','nine-sharing-sign14-95gate-expression-terminal-independent','nine-sharing-sign14-exact-degree-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider-survey.py')],capture_output=True,text=True,check=True,timeout=180);v=json.loads(x.stdout);assert not x.stderr and v['status']=='PASS' and v['overlap_count']==1075 and len(v['extra'])==69
own={'Sign14AxisDiagonalDegree','Sign14AxisDiagonalBinding','Sign14AxisDegreeLower','Sign14ExactDegree'};assert set(v['own'])==own
base=Path('/tmp/nine-sharing-sign14-95gate-expression-check-20261110/lib');tool=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean');states=['nine-sharing-sign14-exact-degree-check','nine-sharing-sign14-axis-seed-degree-check','nine-sharing-sign14-axis-na-binding-check','nine-sharing-sign14-axis-inner-binding-check','nine-sharing-sign14-axis-binding-check','nine-sharing-sign14-axis-na-generic-check','nine-sharing-sign14-axis-degree-generic-check'];checked=[]
for stem in states:
 st=json.loads((root/'research'/stem/'attempt01/state.json').read_text());assert st['status']=='PASS'
 for row in st['rows']:
  for mod,d in row['dependencies'].items():
   if mod=='Init':continue
   rel=mod.replace('.','/')+'.olean';name=mod.split('.')[-1];found= v['own'].get(name) if name in own else v['extra'].get(rel)
   if found is None:
    z=base/rel;assert z.is_file();found={'realpath':str(z.resolve()),'sha256':sha(z)}
   assert found['realpath']==d['realpath'] and found['sha256']==d['sha256'],(row['module'],mod);checked.append((row['module'],mod))
assert any(a=='Sign14ExactDegree' and b.endswith('Sign14AxisDegreeLower') for a,b in checked) and len(checked)>=15
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'exact provider local object closure' in r and 'final producer local binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','exact_local_objects':sorted(own),'captured_direct_edges':len(checked),'overlaps':1075,'extra':69,'scope':'audited captured local closure only; no project-wide transitive trace or Lean/PDF claim'},indent=2))
