#!/usr/bin/env python3
"""Independently recompute a focused paired receipt; no transitive ancestry claim."""
from pathlib import Path
import hashlib,json,os,re,subprocess
D=Path(__file__).resolve().parent;V=D.parent;R=D.parents[3];N=V/'ipra-quartic-model-bridge-replay-v2'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
files=[Path(__file__).resolve(),N/'manifest.json',N/'replay.py',N/'receipt.json'];before={str(p):H(p) for p in files}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
m=json.loads((N/'manifest.json').read_text());r=json.loads((N/'receipt.json').read_text())
assert m['status']=='FROZEN_FOCUSED_INPUT' and r['status']=='MATCHED_PASS' and len(m['order'])==len(set(m['order']))==21
assert len(r['runs'])==2 and r['runs'][0]['run']!=r['runs'][1]['run']
assert all(H(p)==digest for p,digest in r['fixed'].items())
seeds=set(m['order']);seen=set();drift=[]
for n in m['order']:
 row=m['sources'][n];p=N/'sources'/(n.replace('.','/')+'.lean')
 assert p.is_file() and not p.is_symlink() and H(p)==row['sha256']
 assert re.findall(r'^import\s+([A-Z][\w.]*)',p.read_text(),re.M)==row['imports']
 assert all(x not in seeds or x in seen for x in row['imports']);seen.add(n)
 if H(R/row['path'])!=row['sha256']:drift.append(n)
for group in (r['parent_output_guards'],r['fallback_guards'],*(x['guards'] for x in r['runs'])):
 for p,rec in group.items():
  q=Path(p)
  if rec is None:assert not os.path.lexists(q),p
  else:assert q.is_file() and str(q.resolve())==rec['realpath'] and H(q)==rec['sha256'],p
x,y=r['runs'];assert x['rows']==y['rows'] and [row['module'] for row in x['rows']]==m['order']
for run in r['runs']:
 root=Path(run['run']);label=run['label']
 for row in run['rows']:
  n=row['module'];obj=root/'lib'/(n.replace('.','/')+'.olean');log=N/label/'logs'/(n.replace('.','_')+'.log')
  assert row['exit']==0 and row['source_sha256']==m['sources'][n]['sha256'] and H(obj)==row['object_sha256'] and H(log)==row['log_sha256']
  text=log.read_text();assert 'error:' not in text and 'sorryAx' not in text and not re.search(r'\b(?:sorry|admit)\b',text)
  for dep,digest in row['direct_inputs'].items():
   p=Path(dep) if Path(dep).is_absolute() else root/'lib'/dep
   assert p.is_file() and H(p)==digest,(n,dep)
assert {str(p):H(p) for p in files}==before
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()==head
out={'status':'PASS_FOCUSED_RECEIPT_AUDIT','rows':len(m['order']),'source_drift_at_audit':drift,'input_sha256':before,'head':head,'scope':'Frozen sources, recorded objects/logs, direct dependencies and captured present/absent guards only; inherited transitive project/package/dynamic ancestry is not revalidated.'}
p=D/'receipt.json';assert not p.exists();p.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
print('PASS_FOCUSED_RECEIPT_AUDIT',len(m['order']),'rows; source drift',drift)
