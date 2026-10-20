#!/usr/bin/env python3
"""Independent replay of a plain state-fold certificate on open whole tapes.
No imports from the producer, searcher, or symbolic proof engine.
"""
from pathlib import Path
from collections import Counter,deque
from functools import lru_cache
import json,hashlib,sys
H=Path(__file__).resolve().parent
D=Path(sys.argv[1]) if len(sys.argv)>1 else H.parent/'fold_binding';P=D/'fold_0'
def need(v,msg):
 if not v:raise ValueError(msg)
def load_unique(p):
 def unique(pairs):
  x={}
  for k,v in pairs:
   need(k not in x,f'duplicate JSON key {k}');x[k]=v
  return x
 return json.loads(p.read_text(),object_pairs_hook=unique)
def parse(p):
 t={};start=None
 for line in p.read_text().splitlines():
  if line.startswith('#! start '):need(start is None,'duplicate start');start=int(line.split()[-1])
  elif line and not line.startswith('#'):
   q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));need((q,b)not in t and b in (0,1)and w in(0,1)and d in('L','R'),'invalid row');t[q,b]=(w,1 if d=='R'else-1,z)
 states={q for q,b in t};need(set(t)=={(q,b)for q in states for b in(0,1)},'not total');need({z for w,d,z in t.values()}-states=={254},'wrong terminal');need(start in states,'bad start');return t,start,states
old,os,oq=parse(D/'candidate.tm');new,ns,nq=parse(P/'candidate.tm');cert=load_unique(P/'local_proof.json');recipe=load_unique(P/'recipe.json')
keep,drop=recipe['keep'],recipe['drop'];phi=lambda q:keep if q==drop else q
need((len(oq),len(nq),keep,drop)==(224,223,180,18),'wrong fold');need(nq==oq-{drop},'changed state set');need(os==ns==0 and phi(os)==ns,'wrong startup relation')
need(cert['headshift']==0 and cert['tagoffset']is None,'nonplain fold not supported');need(cert['keep']==keep and cert['drop']==drop,'recipe mismatch')
facts={int(q):None if fs is None else{int(k):v for k,v in fs.items()}for q,fs in cert['invariant'].items()};need(set(facts)==oq|{254},'invariant state coverage');need(facts[os]=={},'initial tape constrained')
checks=0;admitted=set()
for (q,b),(w,d,z)in old.items():
 fs=facts[q]
 if fs is None or (0 in fs and fs[0]!=b):continue
 need(all(v in(0,1)for v in fs.values()),'nonbinary fact');need(facts[z]is not None,'reachable target marked impossible')
 for k,value in facts[z].items():need((w if k+d==0 else fs.get(k+d))==value,f'noninductive fact {q}/{b}->{z}@{k}')
 checks+=1;admitted.add((q,b))
@lru_cache(None)
def cover(cubes):
 if any(not c for c in cubes):return True
 if not cubes:return False
 x=min(k for c in cubes for k,v in c)
 for value in(0,1):
  sub=set()
  for c in cubes:
   d=dict(c)
   if x not in d or d[x]==value:sub.add(tuple((k,v)for k,v in c if k!=x))
  if not cover(tuple(sorted(sub))):return False
 return True
seen=set();hist=Counter();maxcoord=0;branches=0;transitions=0
for record in cert['row_proofs']:
 q,b=record['row'];need((q,b)in admitted and(q,b)not in seen,'row coverage/duplicate');seen.add((q,b));w,d,z=old[q,b];base={**facts[q],0:b};cubes=[]
 for leaf in record['branches']:
  env={int(k):v for k,v in leaf['guard'].items()};need(all(v in(0,1)for v in env.values()),'nonbinary guard');need(all(env.get(k)==v for k,v in base.items()),'guard omits or contradicts premise');cubes.append(tuple(sorted((k,v)for k,v in env.items()if k not in base)))
  trace=leaf['trace'];need(len(trace)==leaf['steps']and len(trace)>0,'nonpositive or wrong block length');state=phi(q);head=0;writes={}
  for row in trace:
   need(state!=254,'interior halt');sq,sh,read,write,move,target=row;need(sq==state and sh==head,'trace state/head mismatch');need((write,move,target)==new[state,read],'trace transition mismatch');actual=writes.get(head,env.get(head));need(actual is not None and actual==read,'unguarded/wrong tape read');writes[head]=write;head+=move;state=target;maxcoord=max(maxcoord,abs(sh),abs(head));transitions+=1
  if z==254:need(state==254,'wrong terminal endpoint')
  else:
   need(state==phi(z)and head==d,'wrong mapped endpoint')
   for cell in set(writes)|{0}:
    actual=('bit',writes[cell])if cell in writes else('bit',env[cell])if cell in env else('input',cell)
    expected=('bit',w)if cell==0 else('bit',env[cell])if cell in env else('input',cell)
    need(actual==expected,f'whole-tape endpoint mismatch row{q,b} cell{cell}')
  hist[len(trace)]+=1;branches+=1
 need(cover(tuple(sorted(set(cubes)))),f'incomplete guard partition {q}/{b}')
need(seen==admitted,'missing row contracts');need(checks==cert['invariant_rows']==cert['proved_old_rows'],'claimed row count mismatch');need({str(k):v for k,v in sorted(hist.items())}==cert['block_length_histogram'],'claimed block histogram mismatch')
# Pure graph reachability is an independent structural diagnostic, not a trace proof.
reach={ns};todo=deque([ns])
while todo:
 q=todo.popleft()
 if q==254:continue
 for b in(0,1):
  z=new[q,b][2]
  if z not in reach:reach.add(z);todo.append(z)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=dict(status='PASS_INDEPENDENT_OPEN_WHOLE_TAPE_CERTIFICATE_REPLAY',old_states=len(oq),new_states=len(nq),start=ns,halt=254,keep=keep,drop=drop,invariant_transition_obligations=checks,old_rows_proved=len(seen),exhaustive_guard_branches=branches,block_length_histogram=dict(sorted(hist.items())),literal_transitions_replayed=transitions,largest_absolute_touched_or_final_coordinate=maxcoord,syntactically_reachable_working_states=len(reach-{254}),syntactically_unreachable_working_states=sorted(nq-reach),terminal_graph_reachable=254 in reach,source_identical_to_prefold=sha(D/'sites.json')==sha(P/'sites.json'),source_identical_to_prior_conditional_10000_0=sha(P/'sites.json')==sha(H.parent/'inputs/sites.json'),old_sha256=sha(D/'candidate.tm'),new_sha256=sha(P/'candidate.tm'),source_sha256=sha(P/'sites.json'),certificate_sha256=sha(P/'local_proof.json'),recipe_sha256=sha(P/'recipe.json'),checker_sha256=sha(Path(__file__)),scope='For every binary initial tape and integer initial head, each old step has a positive new block with no interior halt and the exact mapped entire tape/head at nonterminal endpoints. Guard cubes are exhaustively covered, not sampled. This proves the 224-to-223 fold, not source adequacy or the prefold source-runtime implementation; those are separate premises.')
(Path(sys.argv[2]) if len(sys.argv)>2 else H/'local_certificate_replay.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
