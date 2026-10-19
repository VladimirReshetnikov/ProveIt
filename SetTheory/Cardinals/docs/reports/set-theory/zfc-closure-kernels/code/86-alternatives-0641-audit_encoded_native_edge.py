#!/usr/bin/env python3
from pathlib import Path
import sys,itertools,json,hashlib,random
if not __debug__:raise RuntimeError('Assertions required')
OUT=Path(__file__).resolve().parent;A=OUT.parent/'architectures';sys.path.insert(0,str(A))
import encoded_native_edge as E

def parse(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n));assert(q,b)not in t;t[q,b]=w,d,n
 return t
T,start,ret,reject,names=E.compile_step();assert ret==68 and len(T)==136 and parse(A/'encoded_native_edge_68.tm')==T
seen=set();reads={q:set()for q in range(68)};count=accepted=maximum=0
def prepare(records,selected,b,e,g,c):
 anchor=c+g+1;k=1+2*b+e;tape={c}|set(range(anchor,anchor+k))|set(range(anchor+k+1,anchor+6))
 p=anchor+7;starts=[]
 for tag,left,right in records:
  starts.append(p)
  for length in(tag+1,left+3,right+3):tape.update(range(p,p+length));p+=length+1
 tape.remove(starts[selected]);tape|={c-2,c-7,p,p+4};assert c-1 not in tape
 return tape,starts

def check(records,selected,b,e,g,c,steps_of_reuse=1):
 global count,accepted,maximum
 tape,starts=prepare(records,selected,b,e,g,c)
 for _ in range(steps_of_reuse):
  initial=set(tape);q=start;h=starts[selected];steps=0;minhead=h
  while q not in(ret,reject):
   seen.add(q);bit=int(h in tape);reads[q].add(bit);w,d,q=T[q,bit]
   if w:tape.add(h)
   else:tape.discard(h)
   h+=1 if d=='R'else-1;steps+=1;minhead=min(minhead,h);assert steps<1000000
  good=((records[selected][0]>>b)&1)==e;assert(q==ret)==good
  expected=initial|{starts[selected]};child=records[selected][1+b]
  if good:expected.discard(starts[child]);assert h==starts[child]
  assert tape==expected and minhead>=c-1,(records,selected,b,e,g,c,tape^expected)
  count+=1;accepted+=good;maximum=max(maximum,steps)
  if not good:break
  selected=child
rng=random.Random(6819)
for n in range(1,9):
 for _ in range(30):
  records=[(rng.randrange(4),rng.randrange(n),rng.randrange(n))for j in range(n)];selected=rng.randrange(n)
  for b,e,c in itertools.product(range(2),range(2),(-19,5)):
   g=records[selected][1+b]+2;check(records,selected,b,e,g,c)
# Stable header and enough gap permit successive native calls without repairing
# any field/counter/marker. Mode generation is deliberately not asserted here.
for n in range(1,7):
 for b,e in itertools.product(range(2),repeat=2):
  tags=[t for t in range(4)if ((t>>b)&1)==e]
  records=[(rng.choice(tags),rng.randrange(n),rng.randrange(n))for j in range(n)]
  check(records,0,b,e,n+1,11,8)
assert seen==set(range(68))-{reject}
forced_one=[13,40,48,52];forced_zero=[27,28,29,30,43,55,56,63]
assert all(reads[q]=={1}for q in forced_one)and all(reads[q]=={0}for q in forced_zero)
result={'status':'PASS_VALID_FRAME_COMPOSITION','working_states':68,'transition_rows':136,'whole_tape_calls':count,'accepted_calls':accepted,'max_steps':maximum,'operational_states_exercised':len(seen),'fixed_header_reuse_calls':6*4*8,
 'proof_selected_forced_one':forced_one,'proof_selected_forced_zero':forced_zero,'required_left_boundary':'counter left neighbor is zero','table_sha256':hashlib.sha256((A/'encoded_native_edge_68.tm').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256((A/'encoded_native_edge.py').read_bytes()).hexdigest(),'scope':'Single-entry finite edge traversal from a valid prepared frame. No mode update or global proof search implemented.'}
(OUT/'encoded_native_edge_independent_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
