#!/usr/bin/env python3
"""Review sign17 staged degree proposal and source/provider routes without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign17-degree-staged-check';draft=research/'nine-sharing-sign17-degree-staged-draft';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
runner=packet/'run.py';manifest=packet/'source-manifest.json';assert sha(runner)=='f9c1ac34bb19080f8154810c4fe3eabe3395c90d08622c2bdf4f273a143600eb' and sha(manifest)=='572a23be527e3cfdf4369d9967b69344d83657acfdda5ac8b89105b5c5bac97c';rows=json.loads(manifest.read_text())['rows'];names=[f'Sign17SharedDegree{i:02}' for i in range(1,7)]+['Sign17RowDegrees00','Sign17RowDegrees01','Sign17DegreeStructural','Sign17DegreeResiduals','Sign17DegreeCompose'];assert [r['module'].split('.')[-1] for r in rows]==names
seen={'Sign17SyntaxDegree','Sign17SharedDegree00'};source={}
for row,name in zip(rows,names):
 src=packet/'src/DiophantineConsistency'/(name+'.lean');s=src.read_text();source[name]=s;assert sha(src)==sha(draft/(name+'.lean'))==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==row['imports'] and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
 for dep in row['imports']:assert dep.split('.')[-1] in seen
 seen.add(name)
allshared='\n'.join(source[x] for x in names[:6]);assert sorted(int(i) for i in re.findall(r'theorem shared(\d\d)_degree \(p : Fin 4 → ℤ\)',allshared))==list(range(5,35));assert allshared.count('set_option maxHeartbeats 4000000 in')==30
allrows=source['Sign17RowDegrees00']+source['Sign17RowDegrees01'];pairs=re.findall(r'theorem row(\d\d)_degree \(p : Fin 4 → ℤ\) : degree \(row\d\d p\) ≤ (\d+)',allrows);assert pairs==[(f'{i:02}',str(n)) for i,n in enumerate((22,7,22,2,6,5,48,46))]
r=source['Sign17DegreeResiduals'];assert 'degree (SharingSeed17Degree96.firstResidual p) ≤ 48' in r and 'degree e ≤ 48' in r and all(f'row{i:02}_degree p' in r for i in range(8))
c=source['Sign17DegreeCompose'];assert '(Sign17AbstractExpression.expression p).toPolynomial.totalDegree ≤ 96' in c and 'Sign17CurrentExpression.expression.toPolynomial.totalDegree ≤ 96' in c and 'expression_polynomial_degree_le CurrentWindowCarry2011.ports' in c
s=runner.read_text();assert "local=='Sign17SyntaxDegree'" in s and "local=='Sign17SharedDegree00'" in s and "elif local in ('Sign17SharedDegree01'" in s and "elif local in framework['observed']" in s and "'-M3600'" in s and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in s and s.count('check_external_syntax()')>=3 and "sha(P/'source-manifest.json')" in s
check=root/'reviews/nine-sharing-sign17-degree-shared-probe-retry02-terminal-independent/check.py';assert sha(check)=='bc4585b6030b9a7c7cd628882cc7f7da594e9d8b2f9f9f20918c0504858fe8e8';subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'stages':11,'shared_node_bounds':30,'residual_bounds':8,'scope':'source-only candidate for arbitrary-port and current symbolic Fin17 totalDegree ≤ 96; no Lean result or external binding'},indent=2,sort_keys=True))
