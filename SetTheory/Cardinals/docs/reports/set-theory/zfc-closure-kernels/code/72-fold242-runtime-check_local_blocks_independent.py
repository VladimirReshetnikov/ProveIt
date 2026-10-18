"""Second, independent finite-window proof of the three literal folds.
Joins are discovered from the exact tables rather than supplied block traces.
Every read is asserted inside the enumerated footprint; other cells untouched.
"""
from pathlib import Path
import hashlib,itertools,json,sys
if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions required')
import independent_runtime as r
P=Path(__file__).resolve().parent
BASE=P/'baseline243_old.tm'
assert hashlib.sha256(BASE.read_bytes()).hexdigest()=='4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300'
old=r.table(BASE)
def inv(q,h,t):
 if q in {15,18,47,65,171}:return t[h-1]==0
 if q in {91,94}:return t[h-1]==1
 if q==27:return t[h]==0
 if q==50:return t[h-1]==1 or t[h]==1
 return True
implications=0
for q in {q for q,b in old}:
 for values in itertools.product((0,1),repeat=5):
  t=dict(zip(range(-2,3),values))
  if not inv(q,0,t):continue
  w,d,z=old[q,t[0]];t[0]=w;assert inv(z,d,t);implications+=1
assert implications==7640
for values in itertools.product((0,1),repeat=5):assert inv(95,0,dict(zip(range(-2,3),values)))
def prefixes(table,q,t,n):
 h=0;t=t.copy();answer=[]
 for i in range(n):
  if q==254:break
  assert h in t,('Unenumerated tape cell read',q,h)
  w,d,z=table[q,t[h]];t[h]=w;h+=d;q=z
  answer.append((q,h,t.copy()))
 return answer
reports=[]
for candidate,removed in ((1,27),(2,50),(3,171)):
 p=P/f'survivor_{candidate}_old.tm';new=r.table(p)
 assert {q for q,b in old}-{q for q,b in new}=={removed}
 assert len(new)==484 and all(t!=removed for w,d,t in new.values())
 impossible=[];ordinary=[];special=[]
 for key,transition in old.items():
  q,b=key
  if q==removed:continue
  admissible=any(inv(q,0,dict(zip(range(-2,3),values)))and values[2]==b for values in itertools.product((0,1),repeat=5))
  if not admissible:impossible.append(key)
  elif new[key]==transition and transition[2]!=removed:ordinary.append(key)
  else:special.append(key)
 hist={};assignments=0
 for q,b in special:
  for values in itertools.product((0,1),repeat=9):
   t=dict(zip(range(-4,5),values))
   if t[0]!=b or not inv(q,0,t):continue
   # Candidate joins are searched independently, without loading worker schemas.
   lhs=prefixes(old,q,t,2);rhs=prefixes(new,q,t,4)
   matches=[(a+1,z+1,L[0],L[1])for a,L in enumerate(lhs)for z,R in enumerate(rhs)if L==R and L[0]not in(removed,254)and inv(L[0],L[1],L[2])]
   assert matches,('No positive whole-tape join',candidate,q,b,t,lhs,rhs)
   clock_old,clock_new,endq,endh=min(matches)
   # Check no halting intermediate config can be crossed by either chosen block.
   assert all(x[0]!=254 for x in lhs[:clock_old]+rhs[:clock_new])
   k=(q,b,clock_old,clock_new,endq,endh);hist[k]=hist.get(k,0)+1;assignments+=1
 reports.append({'candidate':candidate,'status':'INDEPENDENT_ALL_TAPE_POSITIVE_BLOCK_PASS','table_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'removed_state':removed,'invariant_implications':implications,'ordinary_rows':len(ordinary),'invariant_impossible_rows':impossible,'exceptional_rows':special,'all_admissible_nine_bit_assignments':assignments,'discovered_clock_endpoint_classes':[{'row':list(k[:2]),'old_steps':k[2],'new_steps':k[3],'endpoint_state':k[4],'endpoint_head':k[5],'assignments':v}for k,v in sorted(hist.items())],'checkpoint_relation':'Same state/head/full tape, excluding removed state; old invariant holds','initial':'Invariant vacuous at shared95 for arbitrary head/tape','scope':'All integer heads and all binary tapes, including infinite support, from95','global_argument':'Every old checkpoint has a common ordinary step or one of the exhaustively discovered positive whole-tape joins. Old invariant is one-step inductive. Removed control is never an ordinary target and is covered inside the joins. No join crosses halt. Bounded positive clocks yield both halting directions and cannot collapse an infinite run into finite time.','clock_bounds':'1<=old block<=2,1<=new block<=4','new_Lean_or_Rocq_execution':False})
result={'status':'ALL_THREE_INDEPENDENT_LOCAL_PROOFS_PASS','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'old_table_sha256':hashlib.sha256(BASE.read_bytes()).hexdigest(),'invariant':{'left_zero':[15,18,47,65,171],'left_one':[91,94],'state27_current_zero':True,'state50':'left_one OR current_one'},'candidates':reports}
(P/'local_blocks_independent.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
