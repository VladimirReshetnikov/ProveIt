#!/usr/bin/env python3
"""Reproducible 215-state conditional-selector family and finite proof premises.

The construction copies the accepted ProveIt K215 table and replaces one or
more decoder roles by conditional predecessor-bit selectors.  The mathematical
induction is written in MARKER_PROOF.md.  These checks establish all its finite
hypotheses, not a proof-assistant kernel theorem.
"""
from pathlib import Path
from collections import deque
import itertools,json,hashlib
R=Path(__file__).resolve().parent
BASE=R/'k215.native.tm'
OUT=R/'marker_family'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parse(p):
 T={};st=None
 for line in Path(p).read_text().splitlines():
  if line.startswith('#! start '):st=int(line[9:]);continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert d in('L','R')and b in(0,1)and w in(0,1)
  assert(q,b)not in T;T[q,b]=w,1 if d=='R'else-1,z
 return st,T
def encode(T,st):return '#! start '+str(st)+'\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))
def canonical(T,st,reflect=False):
 Q={q for q,b in T};order=[st];m={st:0}
 for q in order:
  for b in(0,1):
   z=T[q,b][2]
   if z in Q and z not in m:m[z]=len(m);order.append(z)
 assert set(m)==Q,'unreachable graph state'
 m[254]=len(Q)
 return tuple((m[q],b,w,-d if reflect else d,m[z])for q in order for b in(0,1)for w,d,z in[T[q,b]])
SPEC={
 'm124':{'keep':124,'drop':127,'branch':0,'markers':{124:1,127:0},'providers':(8,59)},
 'm160':{'keep':160,'drop':190,'branch':1,'markers':{160:0,190:1},'providers':(86,193)},
 'm052':{'keep':52,'drop':176,'branch':0,'markers':{52:1,176:0},'providers':(185,129)},
}
def build(names):
 st,O=parse(BASE);assert st==0 and sha(BASE)=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
 specs=[SPEC[n]for n in names];mapping={x['drop']:x['keep']for x in specs}
 phi=lambda q:mapping.get(q,q)
 N={k:(w,d,phi(z))for k,(w,d,z)in O.items()}
 for x in specs:
  k,v,b=x['keep'],x['drop'],x['branch'];p0,p1=x['providers']
  N[k,b]=(b,-1,v);N[v,0]=(0,1,p0);N[v,1]=(1,1,p1)
 Q={q for q,b in O};assert len(Q)==215 and set(N)==set(O)
 assert {z for w,d,z in N.values()}-Q=={254}
 proof=[]
 incoming=lambda q:{key:act for key,act in O.items()if act[2]==q}
 for x in specs:
  k,v,b=x['keep'],x['drop'],x['branch']
  assert O[k,1-b]==O[v,1-b]==N[k,1-b]
  for q in(k,v):
   marker=x['markers'][q];inc=incoming(q)
   if(q,b)==(176,0):
    assert inc=={(156,1):(1,1,176),(165,0):(0,1,176),(193,0):(0,1,176)}
    assert incoming(156)=={(189,1):(1,-1,156)}
    assert O[189,1]==(1,-1,156)and O[156,1]==(1,1,176)
    reason='All entrances write0 to predecessor, except189/1;156/1 which forces current1 and cannot enter the exceptional current0 branch.'
   else:
    assert inc and all(w==marker and d==1 for w,d,z in inc.values()),(q,inc)
    reason='Every entrance moves right and writes the required predecessor marker.'
   assert O[q,b][0:2]==(b,1)
   tape={-1:marker,0:b};old=dict(tape);oq,oh=q,0
   w,d,oq=O[oq,old[oh]];old[oh]=w;oh+=d
   nq,nh=phi(q),0
   trace=[]
   for j in range(3):
    assert nh in tape
    val=tape[nh];w,d,nq=N[nq,val];trace.append([nh,val,w,d,nq]);tape[nh]=w;nh+=d
   assert(nq,nh,tape)==(phi(oq),oh,old)
   proof.append({'old_role':q,'exceptional_read':b,'left_marker':marker,'incoming':[[a,c,*act]for(a,c),act in sorted(inc.items())],'marker_reason':reason,'new_trace':trace,'old_steps':1,'new_steps':3,'tape_equal':True,'head_equal':True,'mapped_endpoint':nq})
  assert k!=0 and v!=0
 exceptional={x['keep']for x in specs}|{x['drop']for x in specs}
 assert all(N[phi(q),b]==(w,d,phi(z))for(q,b),(w,d,z)in O.items()if q not in exceptional)
 name='-'.join(names);dest=OUT/name;dest.mkdir(parents=True,exist_ok=True)
 (dest/'machine.native.tm').write_text(encode(N,st))
 order=[st]+sorted(Q-{st});mp={q:i for i,q in enumerate(order)};mp[254]=215
 dense={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in N.items()}
 (dest/'machine.tm').write_text(encode(dense,0))
 (dest/'state_map.json').write_text(json.dumps({'native_to_dense':mp,'simulation_old_to_new':{q:phi(q)for q in sorted(Q|{254})}},indent=2)+'\n')
 canonical(N,st)
 receipt={'status':'FINITE_ALL_TAPE_SIMULATION_PREMISES_PASS','name':name,'baseline_sha256':sha(BASE),'native_sha256':sha(dest/'machine.native.tm'),'dense_sha256':sha(dest/'machine.tm'),'source_unchanged':True,'working_states':215,'transition_rows':430,'changed_rows':[[q,b,list(O[q,b]),list(N[q,b])]for q,b in sorted(O)if O[q,b]!=N[q,b]],'role_map':mapping,'local_blocks':proof,'global_theorem':'For every binary initial tape and integer head, starting in state0: each original step is simulated by1 or3 new steps with exact head/tape equality and mapped control. Halting equivalent.','proof_assistant_checked':False}
 # Finite, complete blank-prefix corroboration, separate from the preceding
 # all-tape proof.  Compare every mapped simulation boundary and final tape.
 special={(q,x['branch'])for x in specs for q in(x['keep'],x['drop'])}
 def step(T,q,h,ones):
  b=int(h in ones);w,d,z=T[q,b]
  if w:ones.add(h)
  else:ones.discard(h)
  return z,h+d
 oq=nq=0;oh=nh=0;ot=set();nt=set();newsteps=0;counts={str(x):0 for x in sorted(special)}
 for i in range(95714):
  row=oq,int(oh in ot);k=3 if row in special else 1
  if k==3:counts[str(row)]+=1
  oq,oh=step(O,oq,oh,ot)
  for j in range(k):nq,nh=step(N,nq,nh,nt)
  newsteps+=k
  assert(nq,nh,nt)==(phi(oq),oh,ot),(i,row)
 assert(oq,oh)==(84,-8)and len(ot)==95
 dq=0;dh=0;dt=set()
 for i in range(newsteps):dq,dh=step(dense,dq,dh,dt)
 assert(dq,dh,dt)==(mp[nq],nh,nt)
 receipt['blank_prefix']={'old_steps':95714,'new_steps':newsteps,'exceptional_counts':counts,'all_old_step_boundaries_compared':True,'native_and_dense_final_tape_equal':True,'dispatcher_native':nq,'dispatcher_dense':dq,'head':nh,'one_cells':sorted(nt)}
 (dest/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
 return name,receipt,N
def main():
 global OUT
 import argparse
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--output',type=Path,help='Fresh output directory for portable reconstruction')
 args=parser.parse_args()
 if args.output is not None:
  OUT=args.output.resolve()
  assert not OUT.exists(),'Output directory must be fresh'
 OUT.mkdir(exist_ok=True)
 results=[]
 for names in [('m124',),('m160',),('m124','m160'),('m052','m124','m160')]:
  n,r,N=build(names);results.append(r)
 (OUT/'result.json').write_text(json.dumps(results,indent=2)+'\n')
 print(json.dumps([{k:r[k]for k in('name','status','native_sha256','working_states')}for r in results],indent=2))
if __name__=='__main__':main()
