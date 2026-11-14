#!/usr/bin/env python3
"""Reproduce a 196-state reader rotation; not an end-to-end Lean/PA proof."""
from pathlib import Path
from hashlib import sha256
from collections import deque
import json
import symbolic_runtime as s

HERE=Path(__file__).resolve().parent
EXPECTED='e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'
PATCH={(100,0):(0,True,213),(100,1):(1,True,174),
       (174,0):(0,True,28),(174,1):(1,True,164)}

def read_native(path):
 table={};starts=[]
 for line in path.read_text().splitlines():
  if line.startswith('#! start '):starts.append(int(line[9:]));continue
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split();key=int(q),int(b);assert key not in table
  table[key]=int(w),d=='R',int(n)
 assert starts==[74]
 return table

def run_blank(table,steps):
 tape=set();state=74;head=0;trace=sha256()
 for step in range(steps):
  assert state!=254
  read=int(head in tape);w,right,n=table[state,read]
  trace.update(f'{state},{head},{read},{w},{int(right)},{n}\n'.encode())
  (tape.add if w else tape.discard)(head);head+=1 if right else -1;state=n
 return state,head,tape,trace.hexdigest()

def clean_frame(path,physical,gap=48,head=-2):
 ones={head-1}|{head+i for i,b in enumerate(path)if b}|{head+gap}
 p=head+gap+1
 for value in physical:
  p+=1;ones.update(range(p,p+value+1));p+=value+1
 return 84,head,ones

def graph_reachable(table):
 seen={74};todo=deque(seen)
 while todo:
  q=todo.popleft()
  for b in(0,1):
   n=table[q,b][2]
   if n!=254 and n not in seen:seen.add(n);todo.append(n)
 return seen

def main():
 assert sha256((HERE/'reference/data/pa196.tm').read_bytes()).hexdigest()==EXPECTED
 s.ROOT=HERE/'reference';original,labels=s.machine();oldsites,oldins=s.program()
 changed=original|PATCH
 stored=read_native(HERE/'candidate/data/rotated196.native.tm')
 assert changed==stored
 assert set(changed)==set(original) and len(changed)==392
 assert all(changed[q,b]==original[q,b]for q in s.BOXSTATES for b in(0,1))
 assert len(graph_reachable(changed))==196
 inv={q:i for i,q in enumerate(labels)}
 dense=''.join(f'{i} {b} {changed[q,b][0]} {"R" if changed[q,b][1] else "L"} {inv[changed[q,b][2]]}\n'
               for i,q in enumerate(labels[:-1])for b in(0,1))
 densepath=HERE/'candidate/data/rotated196.tm';densepath.write_text(dense)
 s.ROOT=HERE/'candidate';sites,ins=s.program()
 assert ins==oldins and len(sites)==3812
 assert [(op,r)for p,op,r in sites]==[(op,r)for p,op,r in oldsites]
 contracts=s.contracts();runtime=s.validate(changed,contracts)
 assert runtime['ok'] and runtime['contracts']==4959
 physical=[0,0,0,0,0,0,2,0,0]+[1]*26
 expected=clean_frame(sites[25][0],physical)
 oldstate,oldhead,oldtape,oldhash=run_blank(original,58154)
 state,head,tape,tracehash=run_blank(changed,58294)
 assert (state,head,tape)==expected==(oldstate,oldhead,oldtape)
 short={'inc':'CI','dec':'CD','halt':'CH','continueTo':'CC','breakTo':'CB'}
 sitefile=HERE/'candidate/sites.json'
 sitefile.write_text(json.dumps([[''.join(map(str,p)),short[op],r]for p,op,r in sites],separators=(',',':'))+'\n')
 bad=lambda ss:[i for i,(p,op,r)in enumerate(ss)if '1000000' in ''.join(map(str,p)) or ''.join(map(str,p)).startswith('0000000')]
 receipt={'status':'COMPUTED_SOURCE_AND_UNIVERSAL_FRAME_PASS',
  'upstream_revision':'407cdc356f6b586635e71ac92be394255f4bfea4',
  'reference_dense_sha256':EXPECTED,
  'candidate_dense_sha256':sha256(dense.encode()).hexdigest(),
  'candidate_native_sha256':sha256((HERE/'candidate/data/rotated196.native.tm').read_bytes()).hexdigest(),
  'source_sites_sha256':sha256(sitefile.read_bytes()).hexdigest(),
  'working_states':196,'transition_rows':392,'graph_reachable_working_states':196,
  'native_start':74,'native_halt':254,'dense_start':0,'dense_halt':196,
  'native_changed_rows':[[q,b,w,'R'if d else'L',n]for(q,b),(w,d,n)in sorted(PATCH.items())],
  'dense_changed_rows':[[inv[q],b,w,'R'if d else'L',inv[n]]for(q,b),(w,d,n)in sorted(PATCH.items())],
  'ordinal_source_control_graph_equal':True,'source_sites':3812,
  'exact_engine_rows_unchanged':True,'universal_runtime':runtime,
  'original_bad_marker_sites':bad(oldsites),'rotated_bad_marker_sites':bad(sites),
  'startup':{'original_steps':58154,'rotated_steps':58294,'state_native':state,'head':head,'gap':48,
   'source_site':25,'source_path':list(sites[25][0]),'physical_file':physical,'one_cells':sorted(tape),
   'trace_sha256':tracehash,'original_trace_sha256':oldhash,'same_complete_clean_frame':True},
  'scope':'Finite startup and an executable symbolic induction checker using the unchanged register-engine contracts. No newly compiled Lean proof and no PA consistency biconditional claimed.'}
 (HERE/'checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps({k:v for k,v in receipt.items()if k not in('startup','native_changed_rows','dense_changed_rows')},indent=2))
if __name__=='__main__':
 if not __debug__: raise RuntimeError('Run without Python -O: assertion checks are required')
 main()
