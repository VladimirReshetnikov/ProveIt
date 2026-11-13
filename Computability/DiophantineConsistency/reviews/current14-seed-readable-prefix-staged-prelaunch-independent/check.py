#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/current14-seed-readable-prefix-staged-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='eb7fbd6efb6adf149c832cb04b81b3746539c59fdd6729041e7cd0be03812072' and sha(p/'source-manifest.json')=='0d90250f655fa6a12c69cf728895a369209c1267eef1197afc66f2f02b29a3e7' and sha(root/'research/current14-seed-readable-prefix-staged-draft/stage.py')=='381fe8b2f656f35e87f6738cc5a33917ff21673586f98fe026a540d44aefdd9e'
reviewed=root/'research/current14-seed-readable-prefix-retry-draft/Current14QuotedPrefix.lean';assert sha(reviewed)=='9f64e92fe3bee828ea7d640bc73252a8509635f2a3de544e9d4343654f138a79';s=reviewed.read_text();q=s.index('/-- Independently transcribed');t=s.index('\ndef quoteSentence',q);end=s.index('\nend DiophantineConsistency.Current14QuotedPrefix',t)
rows=json.loads((p/'source-manifest.json').read_text())['rows'];names=['Current14QuotedPrefixCore','Current14QuotedPrefixQuote','Current14QuotedPrefixEndpoint'];deps=['Sign17ReadableCurrent14Endpoint',names[0],names[1]];assert len(rows)==3
parts=[]
for e,n,dep in zip(rows,names,deps):
 z=p/'src/DiophantineConsistency'/(n+'.lean');text=z.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.'+dep] and sha(z)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',text,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',text);parts.append(text)
assert parts[0]==s[:q]+'\nend DiophantineConsistency.Current14QuotedPrefix\n'
def middle(z):return z.split('open Sign17ReadableCurrent14Endpoint\n\n',1)[1].split('\nend DiophantineConsistency.Current14QuotedPrefix',1)[0]
assert middle(parts[1])==s[q:t] and middle(parts[2])==s[t:end]
assert parts[1].count('#print axioms ')==8 and parts[2].count('#print axioms ')==2
for f in ('current14-seed-readable-prefix-retry-draft-independent','nine-sharing-sign17-readable-current14-endpoint-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and "'-j1'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':3,'scope':'proposed fixed token quotation and named Lean endpoint; no Lean PDF/file parser theorem'},indent=2))
