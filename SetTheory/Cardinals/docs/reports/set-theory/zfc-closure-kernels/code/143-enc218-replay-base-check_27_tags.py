#!/usr/bin/env python3
"""Owned local/static and selected-frame analysis for the state27 return near-hit."""
import collections,json,time
from pathlib import Path
import symbolic_contexts as O
D=Path(__file__).resolve().parent;ROOT=D.parent
T=O.readtm(ROOT/'latest219_baseline/candidate-k219/k219.native.tm')
S=json.loads((ROOT/'latest219_baseline/candidate-k219/sites219.json').read_text())
incoming=lambda q:[(p,b,w,d) for (p,b),(w,d,z) in T.items() if z==q]
assert incoming(27)==[(95,0,0,1),(142,1,0,-1),(162,1,0,-1)]
assert incoming(142)==[(174,1,1,1)] and incoming(162)==[(11,1,1,1)]
# Unique incoming1R writes the exact bit later read after142/162's1L row.
assert incoming(95)==[(84,0,0,1)]
# Independent fresh width9 invariant, all initial tapes from state0.
begin=time.monotonic();width=9;mid=4
facts={q:set() for q,b in T};facts[254]=set();todo=collections.deque()
for n in range(1<<width):
 w=tuple((n>>i)&1 for i in range(width));facts[0].add(w);todo.append((0,w))
points=len(todo);transfers=0
while todo:
 assert points<=100000 and transfers<=1000000 and time.monotonic()-begin<30
 q,w=todo.popleft()
 if q==254:continue
 bit,delta,nxt=T[q,w[mid]];out=list(w);out[mid]=bit
 for incomingbit in [0,1]:
  transfers+=1
  after=tuple(out[1:]+[incomingbit]) if delta==1 else tuple([incomingbit]+out[:-1])
  if after not in facts[nxt]:facts[nxt].add(after);todo.append((nxt,after));points+=1
checks=0
for q,windows in facts.items():
 if q==254:continue
 for w in windows:
  bit,delta,nxt=T[q,w[mid]]
  for incomingbit in [0,1]:
   # Separately construct by coordinate pullback.
   after=tuple(incomingbit if j+delta<0 or j+delta>=width else bit if j+delta==mid else w[j+delta] for j in range(width))
   assert after in facts[nxt];checks+=1
zero27=[w for w in facts[27] if w[mid]==0]
fixed={str(i-mid):next(iter(v)) for i in range(width) if len(v:={w[i] for w in zero27})==1}
# Whole-frame selected proof of the sole decoder leaf using27/0.
schemas,_=O.prove_schemata(T);save=O.Tape.advance;caps=[]
def hook(self,tm,lemmas):
 self.key();src=self.R if self.d==1 else self.L
 if self.q==27 and src[0][:2]==('r',0):caps.append([self.q,self.d,self.L.copy(),self.R.copy()])
 return save(self,tm,lemmas)
O.Tape.advance=hook
old=[]
for positive in [False,True]:
 caps=[];rules,_=O.case(T,schemas,S[0],positive,{})
 for q,dr,L,R in caps:
  assert dr==1
  assert L[:2]==[O.atom(0,2),O.atom(1)] and L[2]==O.B
  assert R[0][0:2]==('r',0)
 old.append({'positive':positive,'symbolic_rules':rules,'27_entries':caps})
# New a1 CB returns, using103/1=1L162: they reach27 with current0,
# immediate-right0 and second-right1. No claim about subsequent dispatch.
frames=json.loads((ROOT/'research218_encoding/RETURN_FULL_CONTRACTS.json').read_text())
M={int(k):v for k,v in json.loads((ROOT/'research218_encoding/NATIVE_TO_LEGACY.json').read_text()).items()}
def trans(xs):return [('r',x[1],tuple(x[2])) if x[0]=='run' else ('l',x[1],x[3]) if x[0]=='list' else tuple(x) for x in xs]
new=[];patch=dict(T);patch[103,1]=(1,-1,162)
for idx in [4570,4588,4602,4711]:
 f=next(f for f in frames if f['site'][0]==idx and f['state']==M[103]);t=O.Tape(103,trans(f['left']),trans(f['right']),f['direction'])
 save(t,patch,{});save(t,patch,{});t.key()
 assert (t.q,t.d)==(27,-1) and t.L[0][:2]==('r',0)
 assert t.R[:2]==[O.atom(0),O.atom(1)]
 new.append({'index':idx,'site':f['site'][1],'27_entry':[t.q,t.d,t.L,t.R]})
report={'status':'STATIC_PREDECESSOR_AND_SELECTED_TAG_CHECKS_PASS','static_conclusion':'Every old27/0 comes from95/0;142/1 and162/1 always arrive27 reading1 on any tape.95 comes only from84/0.','fresh_all_tape_width':width,'closure_points':sum(map(len,facts.values())),'closure_checks':checks,'old27_read0_fixed_offsets':fixed,'old27_read0_windows':len(zero27),'old_C8_frame_cases':old,'new_write1_flag_entries':new,'flag_contract':'Right+2=1 is NOT a discriminator: actual oldCD8 arithmetic revisits27/0 with rightwords01^(62+gap) and001^(61+gap). The leftmarker is the valid static discriminator candidate.','not_claimed':['Global internal84 complete-frame invariant','Patched machine correctness','State deletion','Full6167 recapture'],'seconds':time.monotonic()-begin}
(D/'STATE27_TAG_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['old_C8_frame_cases','new_write1_flag_entries']},indent=2))
