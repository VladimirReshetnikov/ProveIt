from pathlib import Path
from hashlib import sha256
import json
root=Path('research/trace75-bfs-soundness-cone');o=root/'observations/attempt01/result.json'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(o)=='e2d2aa8fd88852c79ad25a8348e7230e81bffea984be0272fb418f08b40d33e2';j=json.loads(o.read_text());assert j['status']=='PASS' and j['runner_sha256']==sha(root/'scan.py') and sha(j['input'])==j['input_sha256']=='ca79d2e68509999cb2a6cd43759e31d656796f09719239c0adac259b7cadb559'
p=json.loads(Path(j['input']).read_text());assert p['status']=='PASS';g=p['closure']['project'];seen=set();boundary=set();q=[j['root']]
while q:
 n=q.pop()
 if n in seen or n in boundary:continue
 if n not in g:boundary.add(n);continue
 seen.add(n);q.extend(g[n]['imports'])
assert j['root']=='DirectBFS80ModelHalt' and len(seen)==739 and seen==set(j['project_ancestors']) and boundary==set(j['outside_boundary']) and boundary<=set(p['closure']['outside'])
seeds={'DirectBFS80Carry','Direct80FixedSlots'};assert set(j['seeds'])==seeds and seeds<=seen;cone=set(seeds)
while True:
 new=cone|{n for n in seen if cone.intersection(g[n]['imports'])}
 if new==cone:break
 cone=new
assert len(cone)==21 and cone==set(j['affected']) and j['root'] in cone
for n in cone:assert j['affected'][n]['imports']==g[n]['imports'] and j['affected'][n]['object_sha256']==g[n]['record']['sha256']
print('PASS: historical halt-root 739 project and',len(boundary),'outside boundary; both named seeds yield exact 21-node reverse dependency cone and all captured import/hash rows match source replay receipt.')
print('Header graph only; not evidence of mathematical minimality, trace75 adaptation, completeness, iPRA or external file binding.')
