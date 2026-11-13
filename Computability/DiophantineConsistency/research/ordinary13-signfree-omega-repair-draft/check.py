from pathlib import Path
from hashlib import sha256
from collections import defaultdict,deque
import json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
PINS={'research/ordinary13-residue-signfree-power-model-draft/ResidueSignFreePower.lean.src': '1c6935eda3ce9ae05d257957d7e2d8f5f3786386aaf618d5a480036113c8bb92', 'research/ordinary13-residue-qbalance-graph-draft/ResidueQBalanceGraph.lean.src': 'd4c6ff3e85231b841395b81dca8d940c14ae588d7b06fa2fe1ed1a4bbe381617', 'research/ordinary13-positive84-power-model-draft/Positive84Power.lean.src': '565b28f2fcecbbc0b0f53d827a3dffc7fe8cd1f5090a8a80375e03242cf60a23', 'research/ordinary13-fixed85-native-composition-draft/manifest.json': 'a4934426329ffedef443a7b6a95bd5fd09d5210c8c9014fb522deed82e65c05e', 'research/ordinary13-signfree-omega-repair-draft/ResidueSignFreePowerRepaired.lean.src': 'dfb531049c859c2f6bd320a7569e1dcb69a9c9f6ddb28f1f8fcc70eb53537c3b'}
for p,h in PINS.items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
f=list(PINS);old=Path(f[0]).read_text();client=Path(f[1]).read_text();new=Path(f[4]).read_text()
assert 'import Mathlib.Tactic.Omega' in old and 'import Mathlib.Tactic.Omega' not in new
assert not re.search(r'\bomega\b',new,re.I)
assert Path('../../.lake/packages/mathlib/Mathlib/Tactic/NormNum.lean').is_file()
assert Path('../../.lake/packages/mathlib/Mathlib/Tactic/Ring.lean').is_file()
assert not Path('../../.lake/packages/mathlib/Mathlib/Tactic/Omega.lean').exists()
assert 'namespace DiophantineConsistency.ResidueSignFreePowerDraft' in old and 'namespace DiophantineConsistency.ResidueSignFreePowerDraft' in new
for name in ['sixteen_of_three_projection','growth_of_coordinates','power_of_oriented_balance']:
 def sig(s):return s.split('theorem '+name,1)[1].split(':= by',1)[0]
 assert sig(old)==sig(new),name
def last(s):return s.split('theorem power_of_oriented_balance ',1)[1].split('\nend DiophantineConsistency.ResidueSignFreePowerDraft',1)[0]
assert last(old)==last(new)
assert all(t in new for t in ['lt_succ_iff_le.mp','mul_le_mul_of_nonneg_left','add_le_add_iff_right','tsub_add_cancel_of_le','add_right_cancel','power_bound'])
assert 'import ResidueSignFreePower' in client and 'ResidueSignFreePowerDraft.growth_of_coordinates' in client and 'ResidueSignFreePowerDraft.power_of_oriented_balance' in client
m=json.loads(Path(f[3]).read_text());nodes=m['local_modules'];reverse=defaultdict(set)
for n,r in nodes.items():
 for dep in r['imports']:
  if dep in nodes:reverse[dep].add(n)
assert reverse['ResidueSignFreePower']=={'ResidueQBalanceGraph'}
seen={'ResidueSignFreePower'};queue=deque(seen)
while queue:
 for n in reverse[queue.popleft()]:
  if n not in seen:seen.add(n);queue.append(n)
affected=[n for n in m['dependency_first_order'] if n in seen]
assert affected[0]=='ResidueSignFreePower' and 'Fixed85Endpoint' in affected
assert len(affected)==38
for q in range(46,121):
 for X in range(1,101):
  if 3*X%q==0:assert X>=16
for n in range(13,100):
 r=n-1;R=2*n-1
 assert r+1==n and r>=2 and R==2*r+1
print(json.dumps({'sha256':PINS,'three_theorem_signatures_unchanged':True,'power_body_unchanged':True,'direct_lexical_consumers':['ResidueQBalanceGraph'],'logical_module_override':'ResidueSignFreePower','reverse_dependency_count_including_override':len(affected),'reverse_dependency_order':affected,'local_replacement_tactic_sources_exist':True,'old_mathlib_omega_source_absent':True,'lean_executed':False,'status':'Inert source alternative and bounded lexical rebuild plan; no staging, provider authentication, Lean or axiom validation.'},sort_keys=True,indent=2))
