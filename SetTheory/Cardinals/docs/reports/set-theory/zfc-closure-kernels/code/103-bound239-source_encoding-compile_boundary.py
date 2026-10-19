from pathlib import Path
from functools import cache
from collections import defaultdict
import json,hashlib
H=Path(__file__).resolve().parent;B=H.parent/'baseline/rotation240'
D=json.loads((H/'mapping.json').read_text());J=json.loads((H/'boundary_success.json').read_text());O=D['structures'];S=J['structures'];C=json.loads((H/'boundary_compile_map.json').read_text());same={int(k):v for k,v in C['same'].items()};live=set(C['live'])
T={}
for line in (B/'zfc_rotation240_old.tm').read_text().splitlines():
 if not line or line.startswith('#'):continue
 q,b,w,d,t=line.split();T[int(q),int(b)]=(int(w),d,int(t))
nq={n:int(q) for q,ns in D['qnodes'].items() for n in ns};Q=set(nq.values())
@cache
def oo(n):
 x=O[n];return (tuple(x),) if isinstance(x[0],str) else oo(x[0])+oo(x[1])
@cache
def on(n):
 x=S[n];return (tuple(x),) if isinstance(x[0],str) else on(x[0])+on(x[1])
flat=defaultdict(list)
for n in range(len(O)):flat[oo(n)].append(n)
match={n:same[n] for n in live if n in same}
for n in sorted(live-set(match)):
 hits=flat[on(n)]
 if len(hits)==1:match[n]=hits[0]
alloc={n:nq[m] for n,m in match.items() if m in nq};available=sorted(Q-set(alloc.values()));fresh=[]
for n in sorted(live-set(alloc)):
 if isinstance(S[n][0],str):continue
 q=available.pop(0) if available else max(set(Tq for Tq,b in T)|set(alloc.values()))+1
 alloc[n]=q;fresh.append((n,q))
print('unmatched allocations',fresh,'unused',available)
NT=dict(T);deferred=[];wanted=defaultdict(set);unmatched_leaves=[]
for n,q in alloc.items():
 old=match.get(n);is_same=n in same
 if is_same:continue
 for b,c in enumerate(S[n]):
  if isinstance(S[c][0],int):
   action=(b,'R',alloc[c])
   if old is not None and T[q,b][1]!='R' and isinstance(O[old][b],int) and c in same and same[c]==O[old][b]:action=T[q,b]
   elif old is not None and T[q,b][1]!='R' and isinstance(O[old][b],int):deferred.append((n,q,b,old,O[old][b],c,T[q,b],action))
  else:
   if old is not None and isinstance(O[O[old][b]][0],str) and tuple(O[O[old][b]])==tuple(S[c]):action=T[q,b]
   elif tuple(S[c])==('CB',1) and b==1:action=(0,'L',33)
   elif tuple(S[c])==('CI',1):action=(b,'R',70)
   else:unmatched_leaves.append((n,q,b,c));continue
  wanted[q,b].add(action)
for key,acts in wanted.items():
 assert len(acts)==1,(key,acts)
 NT[key]=next(iter(acts))
assert not unmatched_leaves,unmatched_leaves
# q120 reads previous bit1 after its right child; q202/1 reproduces old q61/1.
assert T[120,1]==(0,'L',61) and T[61,1]==T[202,1]==(0,'L',33)
NT[120,1]=(0,'L',202)
# New final AX break has four trailing ones; peel them through existing helpers.
assert NT[216,1]==(0,'L',33)
NT[216,1]=(0,'L',120)
for q in available:
 del NT[q,0];del NT[q,1]
badref=[(q,b,row) for (q,b),row in NT.items() if row[2] not in {q for q,b in NT} and row[2]!=254]
print('deferred',deferred,'badref',badref)
assert not badref
raw='#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(NT.items()))
(H/'boundary239_provisional2_old.tm').write_text(raw)
(H/'boundary239_sites.json').write_text(json.dumps(J['sites'],indent=2)+'\n')
res=dict(status='UNVERIFIED_PROVISIONAL',working_states=len(NT)//2,allocation=alloc,unused=available,fresh=fresh,deferred=deferred,changes=[dict(state=q,read=b,old=T.get((q,b)),new=v) for (q,b),v in sorted(NT.items()) if T.get((q,b))!=v],sha256=hashlib.sha256(raw.encode()).hexdigest())
(H/'boundary239_compile.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:v for k,v in res.items() if k not in ['allocation']},indent=2))
