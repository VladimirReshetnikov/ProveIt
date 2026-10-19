"""Independent mapped-state all-tape proof and dense/sparse exact boot.
Candidate data is parsed only; all executed code is self-authored.
"""
from pathlib import Path
import hashlib,itertools,json,sys
if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions required')
import independent_runtime as r
P=Path(__file__).resolve().parent
oldp=P/'baseline242_old.tm';newp=P/'candidate_1_old.tm'
assert hashlib.sha256(oldp.read_bytes()).hexdigest()=='c8ef2f44d25fee6813164cc59ec05061799397da8cf7f0ea7baab63d32d76e02'
assert hashlib.sha256(newp.read_bytes()).hexdigest()=='1fa8526c3c971d5a48868599eaed890f614c5a79256e51622d3e32a64229f3a3'
old=r.table(oldp);new=r.table(newp)
assert len(old)==484 and len(new)==482
assert set(old)-set(new)=={(39,0),(39,1)}
assert {k:v for k,v in new.items()if v!=old[k]}=={(17,0):(0,-1,106),(17,1):(1,-1,37),(46,0):(0,1,17),(50,0):(0,1,17)}
working={q for q,b in new};assert len(working)==241
assert {t for w,d,t in new.values()}-working=={254}
assert all((q,b)in new for q in working for b in(0,1))
incoming={q:sorted(k for k,v in old.items()if v[2]==q)for q in(17,39)}
assert incoming=={17:[(12,1)],39:[(46,0),(50,0)]}
def inv(q,h,t):return(q!=17 or t[h-1]==1)and(q!=39 or t[h-1]==0)
def mapped(q):return 17 if q==39 else q
def step(table,q,h,t):
 assert h in t,('Read outside enumerated footprint',q,h)
 w,d,z=table[q,t[h]];t=t.copy();t[h]=w
 return z,h+d,t
checks=0;hist={};classes={}
for q in sorted({q for q,b in old}):
 for bits in itertools.product((0,1),repeat=5):
  tape=dict(zip(range(-2,3),bits))
  if not inv(q,0,tape):continue
  oq,oh,ot=step(old,q,0,tape);assert inv(oq,oh,ot)
  nq,nh,nt=mapped(q),0,tape.copy()
  for duration in range(1,7):
   assert nq!=254,('New halt before old matching endpoint',q,bits)
   nq,nh,nt=step(new,nq,nh,nt)
   if(nq,nh,nt)==(mapped(oq),oh,ot):break
  else:raise AssertionError(('No positive join',q,bits))
  assert duration in(1,3,5)
  hist[duration]=hist.get(duration,0)+1
  classes.setdefault((q,tape[0]),set()).add(duration);checks+=1
assert checks==7712 and hist=={1:7680,5:8,3:24}
assert {k:sorted(v)for k,v in classes.items()if v!={1}}=={(17,0):[5],(17,1):[3],(39,0):[3],(39,1):[3]}
assert mapped(95)==95 and mapped(254)==254
for bits in itertools.product((0,1),repeat=5):assert inv(95,0,dict(zip(range(-2,3),bits)))
proof={'status':'INDEPENDENT_MAPPED_ALL_TAPE_PASS','old_sha256':hashlib.sha256(oldp.read_bytes()).hexdigest(),'new_sha256':hashlib.sha256(newp.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'old_states':242,'new_states':241,'state_map':'39->17; identity elsewhere including halt','invariant':'old17 has left1; old39 has left0','incoming_inventory':{str(q):v for q,v in incoming.items()},'invariant_implications':checks,'positive_whole_tape_blocks':checks,'clock_histogram':hist,'exceptional_row_durations':{'17/0':5,'17/1':3,'39/0':3,'39/1':3},'every_read_and_write_within_enumerated_window':[-2,2],'arbitrary_exterior_unchanged':True,'global_induction':'The old invariant is initially vacuous at95 and one-step preserved. Every old step is matched by positive1/3/5 new steps with identical complete tape/head and mapped control. No block passes through halt. Positive bounded clocks yield two-way halting equivalence from95 on every binary tape, including infinite support, and every integer head.','clock_formula':'t_new=t_old+4*old_visits(17,0)+2*old_visits(17,1)+2*old_visits(39,0)+2*old_visits(39,1)','new_Lean_or_Rocq_execution':False}
(P/'local_proof.json').write_text(json.dumps(proof,indent=2)+'\n')

order=[95]+sorted(working-{95});ren={q:i for i,q in enumerate(order)}|{254:241}
canon={(ren[q],b):(w,d,ren[t])for(q,b),(w,d,t)in new.items()}
assert set(q for q,b in canon)==set(range(241))
canonical=''.join(f'{q} {b} {w} '+('R'if d==1 else'L')+f' {t}\n'for(q,b),(w,d,t)in sorted(canon.items()))
(P/'candidate_1.tm').write_text(canonical);(P/'renumbering.json').write_text(json.dumps(ren,indent=2)+'\n')
want={-6,176};pos=177
for value in[0,0,0,3,0,0,3,0,0]+[1]*167:
 pos+=1;want.update(range(pos,pos+value+1));pos+=value+1
assert len(want)==351
ones=set();q=95;h=0
for tick in range(408419):
 b=int(h in ones);w,d,q=new[q,b]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d
assert(q,h,ones)==(96,-5,want)
arr=bytearray(1);left=0;head=0;state=0
for tick in range(408419):
 if head<left:arr=bytearray(left-head)+arr;left=head
 if head>=left+len(arr):arr.extend(bytearray(head-left-len(arr)+1))
 w,d,state=canon[state,arr[head-left]];arr[head-left]=w;head+=d
assert(state,head,{left+i for i,b in enumerate(arr)if b})==(ren[96],-5,want)
ones=set();q=95;h=0;visits={k:0 for k in((17,0),(17,1),(39,0),(39,1))}
for tick in range(407979):
 b=int(h in ones)
 if(q,b)in visits:visits[q,b]+=1
 w,d,q=old[q,b]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d
assert(q,h,ones)==(96,-5,want)
extra=4*visits[17,0]+2*sum(v for k,v in visits.items()if k!=(17,0))
assert 407979+extra==408419
boot={'status':'INDEPENDENT_241_WHOLE_BLANK_PASS','working_states':241,'rows':482,'start_canonical':0,'dispatcher_canonical':ren[96],'halt_canonical':241,'canonical_sha256':hashlib.sha256(canonical.encode()).hexdigest(),'old_sha256':hashlib.sha256(newp.read_bytes()).hexdigest(),'blank_steps':408419,'sparse_inherited_and_dense_canonical_whole_tapes_agree':True,'head':-5,'marker':-6,'header':176,'ones':351,'zero_exterior':True,'logical_registers':[3,0,0,0,3,0,0,0,0],'spares_count':167,'spares_values':1,'old242_blank_steps':407979,'clock_formula_extra_steps':extra,'old_blank_exception_visits':{f'{q}/{b}':v for(q,b),v in visits.items()}}
(P/'boot.json').write_text(json.dumps(boot,indent=2)+'\n');print(json.dumps({'local_proof':proof,'boot':boot},indent=2))
