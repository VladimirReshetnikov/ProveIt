#!/usr/bin/env python3
"""Review exact sign23 degree client, its audited provider union, no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign23-exact-degree-check';draft=research/'nine-sharing-sign23-exact-degree-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=packet/'source-manifest.json';assert sha(manifest)=='40f401551eb9c32469f924b7e3398db5ed65c25d0d320af11408d7ac9ed49124'
entry,=json.loads(manifest.read_text())['rows'];src=packet/'src/DiophantineConsistency/Sign23ExactDegree.lean';assert entry['module']=='DiophantineConsistency.Sign23ExactDegree' and sha(src)==sha(draft/src.name)==entry['source_sha256']
s=src.read_text();assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==entry['imports']==['DiophantineConsistency.Sign23DegreeCompose','DiophantineConsistency.Sign23DegreeLower']
assert '(Sign23AbstractExpression.expression p).toPolynomial.totalDegree = 8' in s and 'Sign23CurrentExpression.expression.toPolynomial.totalDegree = 8' in s
assert 'Nat.le_antisymm (Sign23SyntaxDegree.expression_polynomial_degree_le p)' in s and '(Sign23LeadingRows.expression_polynomial_degree_ge p)' in s
assert not re.search(r'(?m)^\s*(axiom|opaque)\b',s)
upper=packet/'upper-survey.py';assert sha(upper)==sha(draft/'upper-survey.py')=='a7bbadf19efbb9e8b3eea8bc282e02e176991d15684f73687c15900e347096d0'
runner=packet/'run.py';assert sha(runner)=='93651267fe42b78e49524ba47f0dff71e28825b62e6f17dfed88e0c1fd9b9d17';r=runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r and "need(not OUT.exists(),'output exists')" in r
assert "need(check_upper()==upper_data,'upper final drift')" in r and "for n,rec in upper_data['objects'].items():" in r
for review in ['nine-sharing-sign23-degree-upper-terminal-independent','nine-sharing-sign23-full-coeff-terminal-independent']:
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
u=subprocess.run([sys.executable,'-I','-S','-B',str(upper)],check=True,capture_output=True,text=True,timeout=120);d=json.loads(u.stdout);assert d['status']=='PASS' and d['overlay_overlap']==1412 and set(d['objects'])=={'Sign23SyntaxDegree','Sign23DegreeStructural','Sign23DegreeResiduals','Sign23DegreeCompose'}
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'upper_overlay_overlap':d['overlay_overlap'],'scope':'proposed abstract and current exact degree 8; no Lean result or external binding'},sort_keys=True,indent=2))
