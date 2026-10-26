"""Bounded semantic QA only: not Lean elaboration or proof certification."""
from pathlib import Path
import hashlib,itertools,json,re
base=Path(__file__).resolve().parent
source=base.parent/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Data.lean'
text=source.read_text()
action_text=text.split('def actionCache : Array Action := #[',1)[1].split(']',1)[0]
actions=[(w=='true',d=='true',int(q)) for w,d,q in re.findall(r'\((true|false), (true|false), (\d+)\)',action_text)]
assert len(actions)==430
lists=text.split('def targetList (d : Bool) : List ℕ :=',1)[1].split('\ndef targets ',1)[0]
rt,lf=re.findall(r'\[([0-9, ]+)\]',lists)
targets={True:list(map(int,rt.split(','))),False:list(map(int,lf.split(',')))}
assert all(sorted(set(q for _,d,q in actions if d==direction))==targets[direction] for direction in [False,True])
def rail(d,q): return 205-199*int(d)+sum(v<q for v in targets[d])
checks=0;halt_checks=0;left_checks=0;right_checks=0
for j,(write,d,target) in enumerate(actions):
 for head in [-5,-1,0,3]:
  nxt=head+(1 if d else -1)
  for read in [0,1]:
   def tile(x):
    if x==head:return ((1-int(d))*rail(False,target),2*(j//2)+j%2+2,int(d)*rail(True,target),int(write))
    if x==nxt:return (int(d)*rail(d,target),read,(1-int(d))*rail(d,target),2*target+read+2)
    return (0,read,0,read)
   def pulse(x):return rail(d,target) if x==(head if d else nxt) else 0
   for x in range(head-4,head+5):
    t=tile(x)
    assert t[0]==pulse(x-1) and t[2]==pulse(x)
    assert tile(x+1)[0]==t[2]
    checks+=1;halt_checks+=target==215;left_checks+=not d;right_checks+=d
# Every Boolean predicate on every open interval with endpoints in [-4,4].
# The two closure conditions are tested precisely on internal adjacent points.
interval_instances=0;satisfying=0
for l in range(-4,5):
 for r in range(l+2,5):
  interior=list(range(l+1,r))
  for seed in interior:
   for mask in range(1<<len(interior)):
    p={x for i,x in enumerate(interior) if mask&(1<<i)}
    nxt=all(x+1 in p for x in interior if x+1<r and x in p)
    prev=all(x-1 in p for x in interior if l<x-1 and x in p)
    if seed in p and nxt and prev:
     assert set(interior)<=p
     satisfying+=1
    interval_instances+=1
# Removing either propagation direction is unsound even in (-3,3).
assert not set(range(-2,3)) <= {0,1,2}
assert not set(range(-2,3)) <= {-2,-1,0}
report={'status':'PASS bounded Python model checks; NOT Lean certification',
 'source_sha256':hashlib.sha256(text.encode()).hexdigest(),
 'action_count':len(actions),'targets_match_actual_action_cache':True,
 'edge_and_matching_samples':checks,'left_move_samples':left_checks,'right_move_samples':right_checks,
 'halt_entry_samples':halt_checks,'head_coordinates':[-5,-1,0,3],
 'point_offsets':[-4,-3,-2,-1,0,1,2,3,4],'plain_and_receiver_bits':[0,1],
 'interval_predicate_seed_instances':interval_instances,'satisfying_interval_instances':satisfying,
 'interval_endpoint_range':[-4,4],
 'limits':['finite translation samples only; integer Lean proof remains uncompiled',
 'does not certify actionCache equals decimal decoder; existing pinned source supplies that theorem',
 'does not certify original arbitrary tapes; edge theorem does not inspect tape bits',
 'does not infer finite-strip walls from constructed whole-integer row']}
(base/'SEMANTIC_CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
