#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2]; repo=root.parents[1]; p=root/'research/nine-sharing-sign14-zero-assembly-retry02-check'; old=root/'research/nine-sharing-sign14-zero-assembly-retry01-check'; sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='5dd8c8f41ecdf7043a3ba09af79af909ccac5593e0c254c0d55fc1a9899f6d23'
assert sha(p/'source-manifest.json')=='3f0dc71b0e1098ecc6493311275411180b93a44fe8b6cb34ae81c25ae1a18f2c'
rows=json.loads((p/'source-manifest.json').read_text())['rows']; oldrows=json.loads((old/'source-manifest.json').read_text())['rows']; assert len(rows)==len(oldrows)==2
for row,prev,name in zip(rows,oldrows,['Sign14ForwardBridge','Sign14ReverseBridge']):
 assert row['module']==prev['module']=='DiophantineConsistency.'+name and row['imports']==prev['imports']
 src=p/'src/DiophantineConsistency'/(name+'.lean'); source=src.read_text(); prior=(old/'src/DiophantineConsistency'/(name+'.lean')).read_text()
 assert prior.replace('open AdaptiveEquationSyntax2011\n','open AdaptiveEquationSyntax2011\nattribute [local irreducible] SharingSeed14Degree124.seed SharingSeed15Degree124.seed\n')==source
 assert sha(src)==sha(repo/row['source'])==row['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',source,re.M)==row['imports']
 assert not re.search(r'(?m)^\s*(axiom|opaque)\b|\b(sorry|admit|native_decide)\b',source)
r=(p/'run.py').read_text(); assert "'-M2800'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
assert all(s in r for s in ('failed state pin','failed outer pin','failed log pin','retry failure state pin','retry failure outer pin'))
check=root/'reviews/nine-sharing-sign14-zero-assembly-retry01-terminal-independent/check.py'; assert sha(check)=='8d65cab8c125bfb682bfe5782d04c271a9e8baa9a6fb7ad187000e3ac811cf4d'; subprocess.run([sys.executable,'-I','-S','-B',str(check)],capture_output=True,check=True,timeout=120)
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180); assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':2,'scope':'conditional pointwise forward/reverse zero assembly; existential iff separate'},indent=2))
