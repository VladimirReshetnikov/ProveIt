from pathlib import Path
from functools import cache
from collections import defaultdict
import json,hashlib,sys
H=Path(__file__).resolve().parent;B=H.parent/'baseline/rotation240'
D=json.loads((H/'mapping.json').read_text());J=json.loads(Path(sys.argv[1]).read_text());O=D['structures'];S=J['structures'];same={};live=set();canon={};I={}
def key(k,db):
 x=db[k];v=tuple(x) if isinstance(x[0],str) else tuple(key(c,db) for c in x)
 if v not in canon:canon[v]=len(canon)
 return canon[v]
for n in range(len(O)):I[key(n,O)]=n
def visit(n):
 if n in live:return
 live.add(n)
 if isinstance(S[n][0],int):
  for c in S[n]:visit(c)
visit(J['root'])
for n in live:
 k=key(n,S)
 if k in I:same[n]=I[k]
PREFIX=sys.argv[2] if len(sys.argv)>2 else 'projection240'
ALLSITES=[];PATHS=defaultdict(list)
def expand(n,p):
 PATHS[n].append(p)
 if isinstance(S[n][0],str):ALLSITES.append([p,*S[n]])
 else:
  for b,c in enumerate(S[n]):expand(c,p+str(b))
expand(J['root'],'')
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
   elif tuple(S[c])==('CB',1) and b==1:
    trailing={len(p+'1')-len((p+'1').rstrip('1')) for p in PATHS[n]}
    assert len(trailing)==1,trailing
    action=(0,'L',{1:48,2:33,3:202,4:120}[next(iter(trailing))])
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
for q in available:
 del NT[q,0];del NT[q,1]
badref=[(q,b,row) for (q,b),row in NT.items() if row[2] not in {q for q,b in NT} and row[2]!=254]
print('deferred',deferred,'badref',badref)
repair=[]
for q in sorted({q for q,b in NT}):
 a,b=NT[q,0],NT[q,1]
 if a[:2]==(0,'R') and b[:2]==(1,'R') and NT.get((a[2],0))==(0,'R',23) and NT.get((b[2],0))==(0,'R',105):repair.append(q)
print('context repair candidates',repair)
if repair:NT[218,0]=(0,'L',repair[0])
assert not badref
raw='#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(NT.items()))
(H/(PREFIX+'_old.tm')).write_text(raw)
(H/(PREFIX+'_sites.json')).write_text(json.dumps(ALLSITES,indent=2)+'\n')
res=dict(status='UNVERIFIED_PROVISIONAL',working_states=len(NT)//2,context_repair=repair,allocation=alloc,unused=available,fresh=fresh,deferred=deferred,changes=[dict(state=q,read=b,old=T.get((q,b)),new=v) for (q,b),v in sorted(NT.items()) if T.get((q,b))!=v],sha256=hashlib.sha256(raw.encode()).hexdigest())
(H/(PREFIX+'_compile.json')).write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:v for k,v in res.items() if k not in ['allocation']},indent=2))
