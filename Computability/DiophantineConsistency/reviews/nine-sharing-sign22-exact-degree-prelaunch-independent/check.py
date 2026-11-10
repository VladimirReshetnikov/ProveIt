#!/usr/bin/env python3
"""Review exact sign22 degree client, its audited provider union, no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign22-exact-degree-check';draft=research/'nine-sharing-sign22-exact-degree-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=packet/'source-manifest.json';assert sha(manifest)=='10cf20aac5590a43387550de40a4f06265d906017fdf115ea0a05739d992be96'
entry,=json.loads(manifest.read_text())['rows'];src=packet/'src/DiophantineConsistency/Sign22ExactDegree.lean';assert entry['module']=='DiophantineConsistency.Sign22ExactDegree' and sha(src)==sha(draft/src.name)==entry['source_sha256']
s=src.read_text();assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==entry['imports']==['DiophantineConsistency.Sign22DegreeCompose','DiophantineConsistency.Sign22DegreeLower']
assert '(Sign22AbstractExpression.expression p).toPolynomial.totalDegree = 12' in s and 'Sign22CurrentExpression.expression.toPolynomial.totalDegree = 12' in s
assert 'Nat.le_antisymm (Sign22SyntaxDegree.expression_polynomial_degree_le p)' in s and '(Sign22LeadingRows.expression_polynomial_degree_ge p)' in s
assert not re.search(r'(?m)^\s*(axiom|opaque)\b',s)
upper=packet/'upper-survey.py';assert sha(upper)==sha(draft/'upper-survey.py')=='2cf9d9d9b99070798076f6141a5040e344c05856aa863ce067f3c56661a455e5'
runner=packet/'run.py';assert sha(runner)=='9d0c5fd25629b9ba2869dd0f4edd6e72c06118ddf7ff702b0e4a5d6c51fd03e2';r=runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r and "need(not OUT.exists(),'output exists')" in r
assert "need(check_upper()==upper_data,'upper final drift')" in r and "for n,rec in upper_data['objects'].items():" in r
for review in ['nine-sharing-sign22-degree-upper-terminal-independent','nine-sharing-sign22-full-coeff-terminal-independent']:
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
u=subprocess.run([sys.executable,'-I','-S','-B',str(upper)],check=True,capture_output=True,text=True,timeout=120);d=json.loads(u.stdout);assert d['status']=='PASS' and d['overlay_overlap']==1426 and set(d['objects'])=={'Sign22SyntaxDegree','Sign22DegreeStructural','Sign22DegreeResiduals','Sign22DegreeCompose'}
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'upper_overlay_overlap':d['overlay_overlap'],'scope':'proposed abstract and current exact degree 12; no Lean result or external binding'},sort_keys=True,indent=2))
