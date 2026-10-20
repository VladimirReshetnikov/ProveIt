"""Independent finite certificates for two novel K221 research avenues.
NO <=220 runtime correctness is claimed. All paths are local research inputs.
"""
from pathlib import Path
import json,hashlib
from collections import deque
D=Path(__file__).resolve().parent
B=D.parents[1]/'research_sub222/delivery/K221_Construction_2026-10-20'
raw=(B/'machine/k221.native.tm').read_bytes();assert hashlib.sha256(raw).hexdigest()=='e6dc479f09ded05dd1c0639b60a0c453483f42e6b77c29562d433cac528c1ecc'
T={}
for line in raw.decode().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
U={(q,b):(w,d,75 if z==50 else z)for(q,b),(w,d,z)in T.items()if q!=50}
assert len(U)==440
# Two separately coded startup simulations with an exact full-support endpoint.
q=h=0;ones=set()
for _ in range(108420):
 bit=int(h in ones);w,d,q=U[q,bit]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d
q2=h2=0;tape={}
for _ in range(108420):
 write,move,nextq=U[(q2,tape.get(h2,0))];tape[h2]=write;h2+=move;q2=nextq
assert(q,h,ones)==(q2,h2,{i for i,b in tape.items()if b})
logical=[4,3,0,0,3,0,0,0,0];phy=[6,2,0,4,3,7,8,5,1];physical=[None]*9
for i,j in enumerate(phy):physical[j]=logical[i]
expected={-7,66};cursor=67
for n in physical+[1]*61:
 cursor+=1;expected.update(range(cursor,cursor+n+1));cursor+=n+1
assert(q,h,ones)==(84,-6,expected)
# Independently compile the binary source to ordinal guarded control flow.
S=json.loads((B/'machine/sites221.json').read_text());assert len(S)==4744

def graph(ss):
 leaf={p:i for i,(p,o,a)in enumerate(ss)};assert len(leaf)==len(ss);prefix={p[:k]for p in leaf for k in range(len(p))};assert not(prefix&leaf.keys());assert all(p+b in prefix or p+b in leaf for p in prefix for b in'01');depth=max(map(len,leaf))
 def locate(p):
  w=p+'0'*depth
  return next(leaf[w[:k]]for k in range(1,len(w)+1)if w[:k]in leaf)
 def inc(p):return format((int(p,2)+1)%(1<<len(p)),f'0{len(p)}b')if p else''
 def cut(p,b,k):
  if not k:return p
  x=[i for i,c in enumerate(p)if c==b]
  return p[:x[-k]]if len(x)>=k else''
 out=[]
 for p,o,a in ss:
  if o=='CI':out.append((o,a,(locate(inc(p)),)))
  elif o=='CD':out.append((o,a,(locate(inc(cut(p,'0',1))),locate(inc(p)))))
  elif o=='CB':out.append(('J',None,(locate(inc(cut(p,'0',a))),)))
  elif o=='CC':out.append(('J',None,(locate(cut(p,'1',a)),)))
  else:assert o=='CH';out.append(('H',None,()))
 return out,locate('')
G,entry=graph(S);facts=[None]*len(S);seed=[3,0,0,0,3,0,0,0,0];facts[entry]=tuple(1<<v for v in seed);queue=deque([entry]);updates=0

def shift(mask,d):
 out=0
 for v in range(9):
  if mask>>v&1:
   if d==1:out|=1<<min(8,v+1)
   elif v==8:out|=(1<<7)|(1<<8)
   elif v:out|=1<<(v-1)
 return out

def edges(i):
 op,r,ts=G[i];a=facts[i]
 if op=='H':return[]
 if op=='J':return[(ts[0],a)]
 if op=='CI':b=list(a);b[r]=shift(a[r],1);return[(ts[0],tuple(b))]
 out=[]
 if a[r]&1:b=list(a);b[r]=1;out.append((ts[0],tuple(b)))
 if a[r]&~1:b=list(a);b[r]=shift(a[r]&~1,-1);out.append((ts[1],tuple(b)))
 return out
while queue:
 i=queue.popleft()
 for j,fs in edges(i):
  n=fs if facts[j]is None else tuple(a|b for a,b in zip(facts[j],fs))
  if n!=facts[j]:facts[j]=n;updates+=1;queue.append(j)
assert facts[4598][6]==facts[4603][6]==facts[4718][1]==1
assert [i for i,f in enumerate(facts)if f is None]==[4604,4719,4720]
# Audit closure, independently of the worklist convergence criterion.
checked=0
for i,f in enumerate(facts):
 if f is None:continue
 for j,a in edges(i):assert all(x&~y==0 for x,y in zip(a,facts[j]));checked+=1
# Exact stuttering CFG quotient for each deletion, with no deleted halt or loop.
variants=[]
for mask in range(1,4):
 removed=({4603,4604}if mask&1 else set())|({4718,4719,4720}if mask&2 else set());keep=[i for i in range(len(S))if i not in removed];mp={x:i for i,x in enumerate(keep)}
 def compress(j):
  used=[]
  while j in removed:
   assert j not in used and facts[j]is not None;used.append(j);op,r,ts=G[j];assert op=='CD'and facts[j][r]==1;j=ts[0]
  return mp[j],used
 ns=json.loads((D/f'drop_seed_noops/{mask}/sites.json').read_text());ng,ne=graph(ns);assert len(ns)==len(keep)
 maxskip=0
 for ni,oi in enumerate(keep):
  assert ns[ni][1:]==S[oi][1:]
  op,r,ts=G[oi];want=[]
  for j in ts:
   # A graph edge entering an unreachable removed node is itself unreachable;
   # none remains as a successor of a kept reachable site in these three cases.
   jj,seq=compress(j);want.append(jj);maxskip=max(maxskip,len(seq))
  assert ng[ni]==(op,r,tuple(want))
 assert ne==compress(entry)[0]
 variants.append(dict(mask=mask,source=str(D/f'drop_seed_noops/{mask}/sites.json'),removed_ordinals=sorted(removed),retained=len(keep),maximum_skipped_reachable_steps=maxskip,quotient_checked=True))
def P(x,y):return(x+y)*(x+y+1)//2+y
# START's least encoded number at a nonnegative tail.
start_min=P(3,P(1,P(1,P(0,0))));assert start_min==32
receipt=dict(status='NOVEL_RESEARCH_CERTIFICATES_PASS_NOT_A_K220_PROOF',baseline_sha256=hashlib.sha256(raw).hexdigest(),shortened_scanner_startup=dict(steps=108420,working_states=220,state=q,head=h,logical_registers=logical,physical_registers=physical,extra_gap=8,spares=[1]*61,one_cells=sorted(ones),complete_tape_equality_two_simulators=True,runtime_valid=False,runtime_counterexample='research_sub221/runtime/delete_50/result.json'),seed_noop_invariant=dict(threshold=8,updates=updates,closure_edges=checked,unreachable=[4604,4719,4720],zero_facts=[[4603,6],[4718,1]],variants=variants),alternative_seed_logic=dict(top_formula=3,formula='E(0,0)',theorem_basis='K221 report: A noncircular derivation of the removed helper',nextproof=4,first_compiled_START_candidate_lower_bound=start_min,scope='Ordinary proof argument, not a newly compiled Rocq endpoint'))
(D/'novel_certificates.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items()if k!='shortened_scanner_startup'},indent=2))
