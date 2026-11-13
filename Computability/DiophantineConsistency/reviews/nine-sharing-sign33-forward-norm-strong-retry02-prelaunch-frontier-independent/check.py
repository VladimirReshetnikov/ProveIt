#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-strong-retry02';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'3fd307ab755cdbdd8de4255c8aae9d7a6e5ea1524897091aa4f36fb91eccc418','provider_survey.py':'df627c4183e693fef590d27c00e7b2925f92244d6a2525c0335fc78a6cccc441','source-manifest.json':'9617eb444f3141c7dd581a043ec14937426f324bcb545c5d329311b207b6baf4'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Sign33ForwardNormStrong38','81d87dfe099c67f1977994ff3aef6ff7e98e90e0b340d89d34c83ba08cfec7c2',['Norm38ReferenceTerminals','Norm38ReferenceFieldsAll','Norm38ForwardGatesAssembly','Norm38ForwardPrefix']),('Sign33ForwardNormStrong','254d3e6ffc0d2c3dd156fbd2d82fcb32127cbc22f86a11581e3e5aea1965b1f5',['Sign33ForwardNormStrong38','Sign33AbstractProjection22','Sign33AbstractProjection28','Sign33AbstractProjection32'])];assert len(rows)==2
for row,(n,h,imports) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.'+x for x in imports]
a=(p/'src/DiophantineConsistency/Sign33ForwardNormStrong38.lean').read_text();b=(p/'src/DiophantineConsistency/Sign33ForwardNormStrong.lean').read_text();old=(d/'research/nine-sharing-sign33-forward-norm-strong-split-check/src/DiophantineConsistency/Sign33ForwardNormStrong.lean').read_text();assert b.replace('Sign33AbstractProjection','Sign33ForwardCoordinate')==old
assert 'Carrier65.strong d = 1' in b and 'ι (v 22)*ι (v 28)-ι (v 32) = ι (v 22)' in b and 'strong_terminal ports u hs' in b
survey=(p/'provider_survey.py').read_text();assert '2464c7f1a7f03d85770c354c5dbb5130c51edf6fdce392e297732373b0cdb8eb' in survey and 'db2eaf9f695f596451f3cefa87f5051b4c2bf56d32c7e43d3c8279c79b0e5932' in survey
run=(p/'run.py').read_text();assert "elif mod in {e['module'] for e in entries}" in run and "need(guard(deps)==row['direct_guard']" in run
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'strong=1 conditional constructor identity; no Lean replay'},indent=2,sort_keys=True))
