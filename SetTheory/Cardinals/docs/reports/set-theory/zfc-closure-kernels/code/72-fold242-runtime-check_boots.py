"""Own exact whole-blank cross-check. Candidate tables are inert data only."""
from pathlib import Path
import hashlib,json,sys
if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions required')
P=Path(__file__).resolve().parent
EXPECTED_HASHES={1:'c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02',2:'e486fd402966944d296fb0abe0ea896f923e28c40c2a9a0226a4ccb408509bd6',3:'211c0eeb9bbf292af817dc4839de6e784e755dc9192f8a2520637f9564f16321'}
EXPECTED_TIMES={1:407979,2:408291,3:407985}
want={-6,176};pos=177
for value in [0,0,0,3,0,0,3,0,0]+[1]*167:
 pos+=1;want.update(range(pos,pos+value+1));pos+=value+1
assert len(want)==351
results=[]
for candidate in (1,2,3):
 path=P/f'survivor_{candidate}_old.tm';raw=path.read_bytes();sha=hashlib.sha256(raw).hexdigest()
 assert sha==EXPECTED_HASHES[candidate]
 table={}
 for line in raw.decode().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t));assert(q,b)not in table and b in(0,1)and w in(0,1)and d in('L','R')
  table[q,b]=(w,1 if d=='R'else-1,t)
 working={q for q,b in table};assert len(working)==242 and len(table)==484
 assert {t for w,d,t in table.values()}-working=={254}
 order=[95]+sorted(working-{95});ren={q:i for i,q in enumerate(order)}|{254:242}
 canonical={(ren[q],b):(w,d,ren[t])for(q,b),(w,d,t)in table.items()}
 expected_canonical=''.join(f'{q} {b} {w} '+('R'if d==1 else'L')+f' {t}\n'for(q,b),(w,d,t)in sorted(canonical.items()))
 assert (P/f'survivor_{candidate}.tm').read_text()==expected_canonical
 assert {int(k):v for k,v in json.loads((P/f'survivor_{candidate}_renumbering.json').read_text()).items()}==ren
 ones=set();q=95;h=0;visited=set()
 for tick in range(1_000_000):
  if (q,h)==(96,-5)and ones==want:break
  assert q!=254
  b=int(h in ones);visited.add((q,b));w,d,t=table[q,b]
  if w:ones.add(h)
  else:ones.discard(h)
  q=t;h+=d
 else:raise AssertionError('Calibrated frame not found')
 assert tick==EXPECTED_TIMES[candidate]
 # Independent dense implementation; canonical rather than inherited labels.
 arr=bytearray(1);left=0;head=0;state=0
 for step in range(tick):
  if head<left:arr=bytearray(left-head)+arr;left=head
  if head>=left+len(arr):arr.extend(bytearray(head-left-len(arr)+1))
  w,d,state=canonical[state,arr[head-left]];arr[head-left]=w;head+=d
 assert(state,head,{left+i for i,b in enumerate(arr)if b})==(ren[96],-5,want)
 result={'candidate':candidate,'status':'EXACT_WHOLE_BLANK_PASS','table_sha256':sha,'canonical_sha256':hashlib.sha256(expected_canonical.encode()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'working_states':242,'rows':484,'blank_transitions':tick,'dense_sparse_canonical_old_agree':True,'root_frame_identical_to_combined243':True,'ones':351,'zero_exterior':True,'start_old':95,'start_canonical':0,'dispatcher_old':96,'dispatcher_canonical':ren[96],'halt_canonical':242,'head':-5,'marker':-6,'header':176,'gap_extra':117,'spare_count':167,'spare_values':1,'logical_seed':[3,0,0,0,3,0,0,0,0],'rows_used':len(visited)}
 results.append(result);(P/f'survivor_{candidate}_boot.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
(P/'all_boots.json').write_text(json.dumps(results,indent=2)+'\n')
