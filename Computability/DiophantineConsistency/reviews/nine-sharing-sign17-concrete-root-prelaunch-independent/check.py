#!/usr/bin/env python3
"""Review concrete staged row-to-gap candidate and provider union without Lean."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];research=root/'research';p=research/'nine-sharing-sign17-concrete-root-check';draft=research/'nine-sharing-sign17-concrete-root-draft';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();m=p/'source-manifest.json';assert sha(m)=='b86e2303e4309e313d6bedb255be6f2deb89f27b00622836ad0044610cad5abd';rows=json.loads(m.read_text())['rows'];names=['Sign17ConcreteRoot','Sign17ConcreteGap'];imports=[['DiophantineConsistency.SharingSeed17Row06','DiophantineConsistency.Sign17RootLift'],['DiophantineConsistency.Sign17ConcreteRoot']];assert [e['module'] for e in rows]==['DiophantineConsistency.'+n for n in names];texts=[]
for e,n,im in zip(rows,names,imports):
 src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();texts.append(s);assert sha(src)==sha(draft/(n+'.lean'))==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']==im and not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit)\b',s)
a,b=texts
assert all('theorem '+x+'_eval' in a for x in ('shared07','shared24','shared26','shared29','shared33')) and all('def '+x+' ' in a for x in ('A','Y','E','B','C'))
assert 'theorem row06_eval' in b and 'theorem exists_from_row06' in b and '(hp : ((p 0 : ℤ) : DiffRing V) = ι beta) (hb : 0 < beta)' in b and '(hNa : (row06 p).evalRing' in b and 'Sign17RootLift.exists_signed_lift' in b
seed=json.loads((research/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json').read_text());assert seed['residuals'][6]['gate']=='Na'
runner=p/'run.py';assert sha(runner)=='c4c265c67a4f626417150d88abbdbee7d940358b91812c3b5553e11f50900769';r=runner.read_text();assert "for n,rec in staged_data['objects'].items():" in r and "if local=='Sign17RootLift':" in r and "elif local=='SharingSeed17Row06':" in r and "elif local in ('Sign17ConcreteRoot',):" in r and "need(check_staged()==staged_data,'staged final drift')" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
for review in ('nine-sharing-sign17-root-lift-terminal-independent','nine-sharing-sign17-staged-syntax-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,capture_output=True,timeout=120)
survey=subprocess.run([sys.executable,'-I','-S','-B',str(p/'staged-survey.py')],check=True,capture_output=True,text=True,timeout=120);d=json.loads(survey.stdout);assert d['status']=='PASS' and d['overlay_overlap']==1057 and len(d['objects'])==17
x=subprocess.run([sys.executable,'-I','-S','-B',str(runner),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','runner_sha256':sha(runner),'staged_objects':len(d['objects']),'overlay_overlap':d['overlay_overlap'],'scope':'concrete staged shared eval and Na-to-gap source under hp/beta>0, no Lean result or full model bridge'},indent=2,sort_keys=True))
