#!/usr/bin/env python3
"""Review exact sign21 degree client, its audited provider union, no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign21-exact-degree-check';draft=research/'nine-sharing-sign21-exact-degree-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=packet/'source-manifest.json';assert sha(manifest)=='33ce54bb003782ad2ae3009ec412ac40c4d9d7107d87478f3a61a63be0317b0c'
entry,=json.loads(manifest.read_text())['rows'];src=packet/'src/DiophantineConsistency/Sign21ExactDegree.lean';assert entry['module']=='DiophantineConsistency.Sign21ExactDegree' and sha(src)==sha(draft/src.name)==entry['source_sha256']
s=src.read_text();assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==entry['imports']==['DiophantineConsistency.Sign21DegreeCompose','DiophantineConsistency.Sign21DegreeLower']
assert '(Sign21AbstractExpression.expression p).toPolynomial.totalDegree = 14' in s and 'Sign21CurrentExpression.expression.toPolynomial.totalDegree = 14' in s
assert 'Nat.le_antisymm (Sign21SyntaxDegree.expression_polynomial_degree_le p)' in s and '(Sign21LeadingRow.expression_polynomial_degree_ge p)' in s
assert not re.search(r'(?m)^\s*(axiom|opaque)\b',s)
upper=packet/'upper-survey.py';assert sha(upper)==sha(draft/'upper-survey.py')=='c7ac7efcd9cda04dd9ac80a344534cec8b23807df024b399b7534f5575acc361'
runner=packet/'run.py';assert sha(runner)=='8db1078a667801eaf29867d4c957cc0611d9a44866b416d6c3291526e6107a36';r=runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r and "need(not OUT.exists(),'output exists')" in r
assert "need(check_upper()==upper_data,'upper final drift')" in r and "for n,rec in upper_data['objects'].items():" in r
for review in ['nine-sharing-sign21-degree-upper-terminal-independent','nine-sharing-sign21-full-coeff-terminal-independent']:
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
u=subprocess.run([sys.executable,'-I','-S','-B',str(upper)],check=True,capture_output=True,text=True,timeout=120);d=json.loads(u.stdout);assert d['status']=='PASS' and d['overlay_overlap']==1440 and set(d['objects'])=={'Sign21SyntaxDegree','Sign21DegreeStructural','Sign21DegreeResiduals','Sign21DegreeCompose'}
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'upper_overlay_overlap':d['overlay_overlap'],'scope':'proposed abstract and current exact degree 14; no Lean result or external binding'},sort_keys=True,indent=2))
