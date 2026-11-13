from pathlib import Path
from hashlib import sha256
from collections import defaultdict,deque
import json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-signfree-omega-repair-independent');A=Path('research/ordinary13-signfree-omega-repair-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
old=Path('research/ordinary13-residue-signfree-power-model-draft/ResidueSignFreePower.lean.src').read_text();new=(A/'ResidueSignFreePowerRepaired.lean.src').read_text()
def sig(s,n):return s.split('theorem '+n,1)[1].split(':= by',1)[0]
for n in ('sixteen_of_three_projection','growth_of_coordinates','power_of_oriented_balance'):assert sig(old,n)==sig(new,n)
assert old.split('theorem power_of_oriented_balance ',1)[1]==new.split('theorem power_of_oriented_balance ',1)[1]
assert 'import Mathlib.Tactic.Omega\n' in old and not re.search(r'\bomega\b',new,re.I)
for p in ('NormNum','Ring'):assert Path('../../.lake/packages/mathlib/Mathlib/Tactic/'+p+'.lean').is_file()
for q in range(46,300):
 for x in range(1,150):
  if q<=3*x:assert x>=16
for n in range(13,300):
 r=n-1;R=2*n-1
 assert r+1==n and r>=2 and R+1==2*n and R==2*r+1
manifest=json.loads(Path('research/ordinary13-fixed85-native-composition-draft/manifest.json').read_text());nodes=manifest['local_modules']; rev=defaultdict(set)
for n,v in nodes.items():
 for dep in v['imports']:
  if dep in nodes:rev[dep].add(n)
assert rev['ResidueSignFreePower']=={'ResidueQBalanceGraph'}
seen={'ResidueSignFreePower'};queue=deque(seen)
while queue:
 for n in rev[queue.popleft()]:
  if n not in seen:seen.add(n);queue.append(n)
order=[n for n in manifest['dependency_first_order'] if n in seen]
assert len(order)==38 and order[0]=='ResidueSignFreePower' and 'Fixed85Endpoint' in seen
pos={x:i for i,x in enumerate(order)}
for n in order:
 for dep in nodes[n]['imports']:
  if dep in seen:assert pos[dep]<pos[n],(n,dep)
client=Path(nodes['ResidueQBalanceGraph']['path']).read_text();assert re.search(r'^import ResidueSignFreePower\s*$',client,re.M)
print(json.dumps({'author_receipt_reproduces':True,'unchanged_three_signatures_and_power_body':True,'finite_positive_projection_controls':True,'finite_predecessor_controls':True,'same_logical_module_consumer_and_reverse_lexical_closure':len(order),'lean_executed':False,'provider_rewire_performed':False},sort_keys=True,indent=2))
