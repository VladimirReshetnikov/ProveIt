#!/usr/bin/env python3
"""Review exact sign21 degree client, its audited provider union, no Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';packet=research/'nine-sharing-sign20-exact-degree-check';draft=research/'nine-sharing-sign20-exact-degree-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=packet/'source-manifest.json';assert sha(manifest)=='5e81a5299ff7f5fad9f6aae9142191d2d819f40a14c212c04a399db074d136d4'
entry,=json.loads(manifest.read_text())['rows'];src=packet/'src/DiophantineConsistency/Sign20ExactDegree.lean';assert entry['module']=='DiophantineConsistency.Sign20ExactDegree' and sha(src)==sha(draft/src.name)==entry['source_sha256']
s=src.read_text();assert re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==entry['imports']==['DiophantineConsistency.Sign20DegreeCompose','DiophantineConsistency.Sign20DegreeLower','DiophantineConsistency.Sign20CurrentBeta']
assert '(hp : p 0 ≠ 0)' in s and 'Sign20CurrentBeta.nonzero' in s
assert '(Sign20AbstractExpression.expression p).toPolynomial.totalDegree = 20' in s and 'Sign20CurrentExpression.expression.toPolynomial.totalDegree = 20' in s
assert 'Nat.le_antisymm (Sign20SyntaxDegree.expression_polynomial_degree_le p)' in s and '(Sign20LeadingRows.expression_polynomial_degree_ge p hp)' in s
assert not re.search(r'(?m)^\s*(axiom|opaque)\b',s)
upper=packet/'upper-survey.py';assert sha(upper)==sha(draft/'upper-survey.py')=='63c3761ab2c0e2189edbdc0f17a4c319cc5ae61a8f2331da80dd4ab47c45b486'
runner=packet/'run.py';assert sha(runner)=='0d8762a85fe80ae47f9410903a68095b605f67b1790707f3ebefa3cb721b5ce1';r=runner.read_text()
assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and '5_000_000_000' in r and "need(not OUT.exists(),'output exists')" in r
assert "need(check_upper()==upper_data,'upper final drift')" in r and "for n,rec in {**upper_data['objects'],**beta_data['objects']}.items():" in r
for review in ['nine-sharing-sign20-degree-upper-terminal-independent','nine-sharing-sign20-count-lower-terminal-independent','nine-sharing-sign20-current-beta-retry-terminal-independent']:
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
u=subprocess.run([sys.executable,'-I','-S','-B',str(upper)],check=True,capture_output=True,text=True,timeout=120);d=json.loads(u.stdout);assert d['status']=='PASS' and d['overlay_overlap']==1455 and set(d['objects'])=={'Sign20SyntaxDegree','Sign20DegreeStructural','Sign20DegreeResiduals','Sign20DegreeCompose'}
beta=packet/'beta-survey.py';assert sha(beta)==sha(draft/'beta-survey.py')=='104719009b329cc907455389892c4e7774a35340838cdd9e04eaa2f8a9ba1037'
b=subprocess.run([sys.executable,'-I','-S','-B',str(beta)],check=True,capture_output=True,text=True,timeout=120);bd=json.loads(b.stdout);assert bd['status']=='PASS' and bd['overlay_overlap']==1455 and set(bd['objects'])=={'Sign20CurrentBeta'}
assert "need(check_beta()==beta_data,'beta final drift')" in r and "elif local=='Sign20CurrentBeta':" in r and "elif local=='Sign20DegreeCompose':" in r and "if local=='Sign20DegreeLower':" in r
p=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert p.returncode==0 and not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'upper_overlay_overlap':d['overlay_overlap'],'scope':'proposed conditional abstract and unconditional current exact degree 20; no Lean result or external binding'},sort_keys=True,indent=2))
