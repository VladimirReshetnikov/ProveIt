#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-93gate-degree-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='67af0c441bdc0382f7e8555379dc7f7ba396ebdb0d144deefb4283ece39f68c6' and sha(p/'provider-survey.py')=='b7deb261a34d7fead87e78a9c50406beafd549b3115401e4c5277006e3503093' and sha(p/'source-manifest.json')=='a0a1cdc284980521a9f810ab9646a904a14d16a3b0462b1b58e410b73df9b636'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign14Optimized93Degree.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign14Optimized93Degree' and e['imports']==['DiophantineConsistency.Sign14Optimized93Expression','DiophantineConsistency.Sign14Optimized94Degree'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('Sign14Optimized93Expression.expression CurrentWindowCarry2011.ports','expression.toPolynomial.totalDegree = 124','Sign14Optimized93Expression.polynomial_eq','Sign14Optimized94Current.totalDegree_eq'):assert t in s
for f in ('nine-sharing-sign14-94gate-degree-terminal-independent','nine-sharing-sign14-93gate-expression-terminal-independent','nine-sharing-sign14-exact-degree-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider-survey.py')],capture_output=True,text=True,check=True,timeout=180);v=json.loads(x.stdout);assert not x.stderr and v['status']=='PASS' and v['overlap_count']==1120 and len(v['extra'])==76
own={'Sign14AxisDiagonalDegree','Sign14AxisDiagonalBinding','Sign14AxisDegreeLower','Sign14ExactDegree'};assert all('DiophantineConsistency/'+name+'.olean' in v['extra'] for name in own)
base=Path('/tmp/nine-sharing-sign14-93gate-expression-check-20261110/lib');tool=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean');states=['nine-sharing-sign14-94gate-degree-check','nine-sharing-sign14-95gate-degree-check','nine-sharing-sign14-exact-degree-check','nine-sharing-sign14-axis-seed-degree-check','nine-sharing-sign14-axis-na-binding-check','nine-sharing-sign14-axis-inner-binding-check','nine-sharing-sign14-axis-binding-check','nine-sharing-sign14-axis-na-generic-check','nine-sharing-sign14-axis-degree-generic-check'];checked=[]
for stem in states:
 st=json.loads((root/'research'/stem/'attempt01/state.json').read_text());assert st['status']=='PASS'
 for row in st['rows']:
  for mod,d in row['dependencies'].items():
   if mod=='Init':continue
   rel=mod.replace('.','/')+'.olean';name=mod.split('.')[-1];found=v['extra'].get(rel)
   if found is None:
    z=base/rel;assert z.is_file();found={'realpath':str(z.resolve()),'sha256':sha(z)}
   assert found['realpath']==d['realpath'] and found['sha256']==d['sha256'],(row['module'],mod);checked.append((row['module'],mod))
assert any(a=='Sign14ExactDegree' and b.endswith('Sign14AxisDegreeLower') for a,b in checked) and len(checked)>=15
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'ingredient hash' in r and 'direct producer binding' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','exact_local_objects':sorted(own),'captured_direct_edges':len(checked),'overlaps':1120,'extra':76,'scope':'audited captured local closure only; no project-wide transitive trace or Lean/PDF claim'},indent=2))
