"""Self-authored finite exhaustive verifier of local all-tape stuttering identities.
The enumeration covers every assignment in the read/write footprint. Every cell
outside that footprint is untouched, so the identities quantify over full tapes.
No packet executable is imported. Global argument is in LOCAL_PROOFS.md.
"""
from pathlib import Path
import json,hashlib,itertools,sys
if not __debug__ or sys.flags.optimize:raise RuntimeError("Enabled assertions are required")
P=Path(__file__).parent

def table(path):
 t={}
 for line in path.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,r=line.split();key=(int(q),int(b));assert key not in t;t[key]=(int(w),1 if d=='R'else-1,int(r))
 return t
base=table(P/'baseline243_old.tm');states=sorted({q for q,b in base});assert len(states)==243 and len(base)==486
left0={15,18,47,65,171};left1={91,94}
def invariant(q,h,s):
 if q in left0:return h-1 not in s
 if q in left1:return h-1 in s
 if q==27:return h not in s
 if q==50:return h-1 in s or h in s
 return True

def run(t,q,s,n):
 s=set(s);h=0;trace=[]
 for tick in range(n):
  assert -4<=h<=4,('footprint escape',q,h);b=int(h in s);assert(q,b)in t
  w,d,r=t[q,b];trace.append((q,h,b,w,d,r))
  if w:s.add(h)
  else:s.discard(h)
  h+=d;q=r
 return q,h,s,trace
# Guard preservation checks require just offsets-2..2, including every possible
# destination-relative guard cell after a single L/R transition.
invchecks=0;by_state={}
for q in states:
 count=0
 for mask in range(32):
  s={j-2 for j in range(5)if mask>>j&1}
  if not invariant(q,0,s):continue
  b=int(0 in s);w,d,r=base[q,b];s.discard(0)
  if w:s.add(0)
  assert invariant(r,d,s),('invariant not closed',q,mask,r,d)
  invchecks+=1;count+=1
 by_state[str(q)]=count
assert all(invariant(95,0,{j-2 for j in range(5)if m>>j&1})for m in range(32))
# Each schema is(rowstate,read,requiredrightbit_or_None,oldsteps,newsteps).
# Old27/read1 is impossible and omitted when27 is retained as the overlay state.
defs=[
 {'name':'fold15_27','serial':1,'removed':27,'schemas':[(15,0,None,1,3),(18,0,None,2,2),(47,0,None,2,2),(65,0,None,2,2)]},
 {'name':'fold27_50','serial':2,'removed':50,'schemas':[(34,1,0,2,4),(34,1,1,2,2),(127,1,0,2,4),(127,1,1,2,2),(91,1,None,2,2),(94,1,None,2,2)]},
 {'name':'fold27_171','serial':3,'removed':171,'schemas':[(150,0,0,2,4),(150,0,1,2,2)]}
]
reports=[]
for spec in defs:
 source=P/f"focus27/survivor_{spec['serial']}_old.tm";new=table(source);removed=spec['removed'];assert len(new)==484;assert {q for q,b in new}==set(states)-{removed};assert all(r[2]!=removed for r in new.values());out=P/'candidates'/spec['name'];out.mkdir(parents=True,exist_ok=True);(out/'machine_old.tm').write_bytes(source.read_bytes())
 starts={(q,b)for q,b,*_ in spec['schemas']};schemas=[];observed=set();used_old=set();used_new=set();ordinary=0;impossible=[]
 for q in states:
  if q==removed:continue
  for b in(0,1):
   admissible=any(invariant(q,0,{j-2 for j in range(5)if m>>j&1})and((m>>2)&1)==b for m in range(32))
   if not admissible:impossible.append([q,b]);continue
   if(q,b)in starts:continue
   assert base[q,b]==new[q,b],('nonordinary',spec['name'],q,b);assert base[q,b][2]!=removed;ordinary+=1
 for q,b,right,oldn,newn in spec['schemas']:
  count=0;ends=set()
  for mask in range(512):
   s={j-4 for j in range(9)if mask>>j&1}
   if not invariant(q,0,s)or int(0 in s)!=b or right is not None and int(1 in s)!=right:continue
   oq,oh,os,ot=run(base,q,s,oldn);nq,nh,ns,nt=run(new,q,s,newn)
   assert(oq,oh,os)==(nq,nh,ns),(spec['name'],q,b,right,mask,ot,nt)
   assert oq!=removed and invariant(oq,oh,os);assert all(row[0]!=254 for row in ot+nt)
   used_old|={(x[0],x[2])for x in ot};used_new|={(x[0],x[2])for x in nt};ends.add((oq,oh));count+=1;observed.add((q,b,mask))
  assert count;schemas.append({'row':[q,b],'right_bit':right,'old_steps':oldn,'new_steps':newn,'all_9bit_assignments_checked':count,'end_state_and_displacement':sorted(ends)})
 # Check every invariant-admissible footprint of every exceptional start is covered.
 for q,b in starts:
  for mask in range(512):
   s={j-4 for j in range(9)if mask>>j&1}
   if invariant(q,0,s)and int(0 in s)==b:assert(q,b,mask)in observed
 order=[95]+sorted(set(states)-{95,removed});ren={q:i for i,q in enumerate(order)}|{254:242};canonical='#! start 0\n'+''.join(f'{ren[q]} {b} {w} {"R"if d==1 else "L"} {ren[r]}\n'for q in order for b in(0,1)for w,d,r in[new[q,b]])
 (out/'machine.tm').write_text(canonical);(out/'renumbering.json').write_text(json.dumps({'old_to_canonical':ren},indent=2)+'\n')
 changes=[{'row':[q,b],'old':base[q,b],'new':r}for(q,b),r in new.items()if base[q,b]!=r]
 report={'status':'PASS_ALL_TAPE_LOCAL_STUTTERING','name':spec['name'],'working_states':242,'deleted_old_state':removed,'base_old_sha256':hashlib.sha256((P/'baseline243_old.tm').read_bytes()).hexdigest(),'old_table_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'canonical_sha256':hashlib.sha256(canonical.encode()).hexdigest(),'initial_state_old':95,'dispatcher_canonical':ren[96],'halt_canonical':242,'invariant_checks':invchecks,'invariant':{'left0_states':sorted(left0),'left1_states':sorted(left1),'state27_current_bit':0,'state50':'left1 or current1','all_other_states':'true'},'excluded_checkpoint_state':removed,'ordinary_rows':ordinary,'invariant_impossible_rows':impossible,'schemas':schemas,'old_max_block_steps':max(x[3]for x in spec['schemas']),'new_max_block_steps':max(x[4]for x in spec['schemas']),'minimum_steps_each_side':1,'footprint_offsets':[-4,4],'outside_footprint':'never read or written by any exceptional block','old_rows_in_schemas':sorted(used_old),'new_rows_in_schemas':sorted(used_new),'patches':changes,'conclusion_scope':'Positive bounded whole-tape stuttering from inherited95 with arbitrary head and arbitrary binary tape, assuming the explicit finite checker and global induction argument. Not a proof-assistant kernel theorem.'}
 (out/'local_proof.json').write_text(json.dumps(report,indent=2)+'\n');reports.append(report);print(spec['name'],ordinary,len(schemas),sum(x['all_9bit_assignments_checked']for x in schemas),report['canonical_sha256'],flush=True)
(P/'local_proofs.json').write_text(json.dumps({'invariant_checks':invchecks,'by_state':by_state,'candidates':reports},indent=2)+'\n')
