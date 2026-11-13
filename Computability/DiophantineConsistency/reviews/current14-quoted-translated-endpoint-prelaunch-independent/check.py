#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-quoted-translated-endpoint-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();assert sha(p/'run.py')=='a93af0bb5f4d2fed95ecfc75b5e4af71fa74ce23a7f2815c0013c6d2d6738d52' and sha(p/'source-manifest.json')=='210856fd0f2bdd861376466f3643ae0d9d62ac19009dcaf1eec8188f8f1242ac'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Current14QuotedTranslatedEndpoint';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Current14QuotedPrefixEndpoint'] and sha(q)==sha(repo/e['source'])==e['source_sha256']=='90a459830c2b41085faa6d932ce2d83e00b7479e7e11a113665f53f1c80d3965' and re.findall(r'^import (\S+)$',s,re.M)==e['imports']
for f in ('current14-quoted-translated-endpoint-source-independent','current14-seed-readable-prefix-staged-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and "env['LEAN_NUM_THREADS']='1'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'direct producer ' in r and 'provider Init binding' in r and "for n,row in provider_names.items():" in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'proposed quoted sentence standard-iPRA derivable iff mapped GG Foundation ZFC consistency; no proof either side/TeX PDF binding'},indent=2))
