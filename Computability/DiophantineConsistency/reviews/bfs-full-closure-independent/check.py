from pathlib import Path
from hashlib import sha256
import json,os
base=Path('research/ten-positive-80-bfs-full-closure'); obs=base/'observations/attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 assert p.is_file(),p
 return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),'link':os.readlink(p) if p.is_symlink() else None}
p=obs/'result.json';assert sha(p)=='1b41178b0123d25e8814b6d430c1f996c90765fc5f1517283d4248b787dc6e1b';j=json.loads(p.read_text())
assert sha(base/'scan.py')==j['scanner_sha256']=='3658994c8e9f9e7c1599c7f8fdb13e96d662184c7e46d0da190883a639fec1a4'
for p,h in j['pins'].items():assert sha(p)==h
prior=json.loads(Path('research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json').read_text())['closure']
root=json.loads(Path('research/ten-positive-80-bfs-displayed-full-ipra/observations/attempt01/terminal.json').read_text())
for p,r in root['pins'].items():assert rec(p)['sha256']==r['sha256'] and str(Path(p).resolve())==r['resolved']
c=j['closure']; project=c['project'];outside=c['outside']; assert j['status']=='PASS_CAPTURE' and c['roots']==['BFSDisplayedFullIPRA']
assert len(project)==1807 and len(outside)==80 and c['header_batches']==71
assert set(prior['project']) <= set(project) and len(prior['project'])==1795 and set(prior['outside'])==set(outside)
assert set(j['matched_prior'])==set(prior['project']) and not j['mismatched_prior'] and not j['outside_mismatch']
assert set(j['new_project'])==set(project)-set(prior['project']) and len(j['new_project'])==12
for n,v in project.items():
 if n in prior['project']:
  assert v['imports']==prior['project'][n]['imports'] and v['companions']==prior['project'][n]['companions'],n
for n,v in outside.items():assert v['companions']==prior['outside'][n]['companions'],n
paths=[Path(x) for x in j['paths']]
for n,v in project.items():
 path=next((p/Path(n.replace('.','/')+'.olean') for p in paths if (p/Path(n.replace('.','/')+'.olean')).is_file()),None)
 assert path is not None and str(path)==v['path'] and rec(path)==v['record'],n
 stem=str(path)[:-6]
 for suffix,record in v['companions'].items():assert rec(stem+suffix)==record,(n,suffix)
for n,v in outside.items():
 path=Path(v['path']);assert rec(path)==v['record'];stem=str(path)[:-6]
 for suffix,record in v['companions'].items():assert rec(stem+suffix)==record,(n,suffix)
seen=set();front=list(c['roots'])
while front:
 n=front.pop()
 if n in seen:continue
 assert n in project or n in outside,n
 seen.add(n)
 if n in project:front.extend(project[n]['imports'])
assert seen==set(project)|set(outside),(len(seen),len(project),len(outside))
headers={}
for i in range(71):
 stem=obs/f'selected-headers-{i:03}';r=json.loads(stem.with_suffix('.json').read_text());so=stem.with_suffix('.stdout');se=stem.with_suffix('.stderr')
 assert r['exit']==0 and r['reason'] is None and sha(so)==r['stdout_sha256'] and sha(se)==r['stderr_sha256'] and not se.read_text()
 cur=None; names={project[n]['path']:n for n in project}
 for line in so.read_text().splitlines():
  if line.startswith('BEGIN '):assert cur is None and line[6:] in names;cur=names[line[6:]];assert cur not in headers;headers[cur]=[]
  elif line.startswith('IMPORT ') and cur is not None:headers[cur].append(line[7:])
  elif line=='END' and cur is not None:cur=None
  else:raise AssertionError((i,line))
 assert cur is None
assert set(headers)==set(project)
for n,h in headers.items():assert h==project[n]['imports'],n
assert root['output']==project['BFSDisplayedFullIPRA']['path'] and root['output_sha256']==project['BFSDisplayedFullIPRA']['record']['sha256']
for n in set(j['new_project'])-{'BFSDisplayedFullIPRA'}:
 v=project[n]; assert v['path'] in root['pins'] and root['pins'][v['path']]['sha256']==v['record']['sha256'] and root['pins'][v['path']]['resolved']==v['record']['resolved'],n
print('PASS: 1807 reachable project headers; 1795 prior imports and complete companion records match; 12 new including root; 80 outside companion records match prior; 71 retained header batches reproduced.')
print('11 non-root new selected object paths and hashes match root compile-run pins; root output matches its own output receipt.')
print('Recheck is post-hoc; reader header reports, producer-time transitive imports/companions, historical/supplemental/package/dynamic ancestry, external file binding remain separate.')

reco=base/'observations/reconcile01'; q=json.loads((reco/'terminal.json').read_text())
assert sha(reco/'terminal.json')=='4232749bb263e43da1a17f65761a20470f5be466aacecb83ce64af07b03590e0'
assert q['exit']==0 and sha(base/'reconcile.py')==q['script_sha256'] and sha(reco/'stdout')==q['stdout_sha256'] and sha(reco/'stderr')==q['stderr_sha256'] and not (reco/'stderr').read_text()
z=json.loads((reco/'stdout').read_text()); assert z['status']=='PASS' and {x['module'] for x in z['new_selected']}==set(j['new_project'])
for x in z['new_selected']:
 row=project[x['module']];assert x['path']==row['path'] and x['sha256']==row['record']['sha256'] and x['resolved']==row['record']['resolved'] and x['imports']==row['imports']
print('PASS: retained author reconciliation receipt and 12 rows checked; root is separately reported output, 11 others are input pins.')
