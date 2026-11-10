#!/usr/bin/env python3
"""Review exact sign24 degree client, its audited provider union, no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign24-exact-degree-check';draft=research/'nine-sharing-sign24-exact-degree-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=packet/'source-manifest.json';assert sha(manifest)=='4ddf252ebc42d5491239f9e8ee7f73f251a35a80ec9d96d3565558d0be519004'
entry,=json.loads(manifest.read_text())['rows'];src=packet/'src/DiophantineConsistency/Sign24ExactDegree.lean';assert entry['module']=='DiophantineConsistency.Sign24ExactDegree' and sha(src)==sha(draft/src.name)==entry['source_sha256']
s=src.read_text();assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==entry['imports']==['DiophantineConsistency.Sign24DegreeCompose','DiophantineConsistency.Sign24DegreeLower']
assert '(Sign24AbstractExpression.expression p).toPolynomial.totalDegree = 8' in s and 'Sign24CurrentExpression.expression.toPolynomial.totalDegree = 8' in s
assert 'Nat.le_antisymm (Sign24SyntaxDegree.expression_polynomial_degree_le p)' in s and '(Sign24LeadingN0.expression_polynomial_degree_ge p)' in s
assert not re.search(r'(?m)^\s*(axiom|opaque)\b',s)
upper=packet/'upper-survey.py';assert sha(upper)==sha(draft/'upper-survey.py')=='264e74545a9f70c066ab7b4a9953c5e90fb9094ae13ea2b90b9689773477cdce'
runner=packet/'run.py';assert sha(runner)=='4fb61ec5a61a1285c74b4e540c1d05cd4fa7625bfd60103be6939227b44113a3';r=runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r and "need(not OUT.exists(),'output exists')" in r
assert "need(check_upper()==upper_data,'upper final drift')" in r and "for n,rec in upper_data['objects'].items():" in r
for review in ['nine-sharing-sign24-degree-structured-retry02-terminal-independent','nine-sharing-sign24-full-coeff-retry02-terminal-independent']:
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
u=subprocess.run([sys.executable,'-I','-S','-B',str(upper)],check=True,capture_output=True,text=True,timeout=120);d=json.loads(u.stdout);assert d['status']=='PASS' and d['overlay_overlap']==1398 and set(d['objects'])=={'Sign24SyntaxDegree','Sign24DegreeStructural','Sign24DegreeResiduals','Sign24DegreeCompose'}
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'upper_overlay_overlap':d['overlay_overlap'],'scope':'proposed abstract and current exact degree 8; no Lean result or external binding'},sort_keys=True,indent=2))
