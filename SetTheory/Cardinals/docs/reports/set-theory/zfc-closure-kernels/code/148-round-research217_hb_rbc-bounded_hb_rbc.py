"""Fresh bounded native-code-schema experiment, not received project code.
Generic constructor unification is sound but intentionally incomplete for arithmetic
and for the sole I(0,0)=0 alias. A found proof must be independently replayed.
"""
import json, heapq, time
from pathlib import Path
OUT=Path(__file__).parent
MAX_FORMS=1200; MAX_ATTEMPTS=150000; MAX_SIZE=95; MAX_SECONDS=19
T='T'
def node(k,a,b):
 if k=='I' and a==T and b==T:return T
 return (k,a,b)
def I(a,b):return node('I',a,b)
def R(a,b):return node('R',a,b)
def Q(a,b):return node('Q',a,b)
def E(a,b):return node('E',a,b)
F=R(T,T)
def N(a):return I(a,F)
def Ex(i,a):return N(Q(i,N(a)))
def L(a,b,c):return I(I(I(c,R(b,c)),a),I(I(a,c),I(b,c)))
def HB(a,b,c):return I(I(I(c,b),a),I(I(a,c),I(b,c)))
def size(t):return 1 if not isinstance(t,tuple) else 1+size(t[1])+size(t[2])
def canonical(t):
 m={}
 def go(x):
  if isinstance(x,int):
   if x not in m:m[x]=len(m)
   return m[x]
  return node(x[0],go(x[1]),go(x[2])) if isinstance(x,tuple) else x
 return go(t)
def shift(t,n):return t+n if isinstance(t,int) else node(t[0],shift(t[1],n),shift(t[2],n)) if isinstance(t,tuple) else t
def apply(t,s):
 if isinstance(t,int) and t in s:return apply(s[t],s)
 return node(t[0],apply(t[1],s),apply(t[2],s)) if isinstance(t,tuple) else t
def unify(x,y):
 todo=[(x,y)];s={}
 def head(t):
  while isinstance(t,int) and t in s:t=s[t]
  return t
 def occurs(v,t):
  t=head(t)
  return t==v or isinstance(t,tuple) and (occurs(v,t[1]) or occurs(v,t[2]))
 while todo:
  a,b=map(head,todo.pop())
  if a==b:continue
  if isinstance(a,int):
   if occurs(a,b):return None
   s[a]=b
  elif isinstance(b,int):
   if occurs(b,a):return None
   s[b]=a
  elif a==T and isinstance(b,tuple) and b[0]=='I':todo.extend(((b[1],T),(b[2],T)))
  elif b==T and isinstance(a,tuple) and a[0]=='I':todo.extend(((a[1],T),(a[2],T)))
  elif isinstance(a,tuple) and isinstance(b,tuple) and a[0]==b[0]:todo.extend(((a[1],b[1]),(a[2],b[2])))
  else:return None
 return s
def detach(ma,mi):
 if not isinstance(ma,tuple) or ma[0]!='I':return None
 mi=shift(mi,1000)
 s=unify(ma[1],mi)
 if s is None:return None
 try:r=canonical(apply(ma[2],s))
 except RecursionError:return None
 return (r,s) if size(r)<=MAX_SIZE else None
def subsumes(p,t):
 todo=[(p,t)];s={}
 while todo:
  a,b=todo.pop()
  if isinstance(a,int):
   if a in s and s[a]!=b:return False
   s[a]=b
  elif isinstance(a,tuple) and isinstance(b,tuple) and a[0]==b[0]:todo.extend(((a[1],b[1]),(a[2],b[2])))
  elif a!=b:return False
 return True
seeds=[('truth',T),('L_bc',L(0,1,2)),('H_B',HB(0,1,2)),('r1',Ex(0,E(0,1))),
 ('r2',I(Q(0,I(1,2)),I(Q(0,1),Q(0,2)))),
 ('r3',I(E(0,1),I(R(2,0),R(2,1)))),('r4',I(Q(0,Q(1,2)),Q(1,Q(0,2)))),
 ('r5',I(E(2,0),I(R(2,1),R(0,1)))),('r6',I(Ex(0,Q(0,1)),1)),
 ('G',I(E(2,0),I(E(2,1),Q(R(0,1),E(0,1)))))]
# Unconditional raw-code schemas only: no bundle or vacuity projection is assumed.
targets={canonical(I(0,0)):'identity',canonical(I(0,I(1,0))):'K',canonical(I(F,0)):'explosion',
 canonical(I(I(I(0,1),0),0)):'Peirce',canonical(I(I(0,1),I(I(1,2),I(0,2)))):'B',
 canonical(I(I(0,I(1,2)),I(I(0,1),I(0,2)))):'S',canonical(E(0,0)):'equality_reflexivity'}
forms=[];parents=[];active=set();where={};heap=[];done=set();found={};attempts=0
start=time.monotonic()
def add(t,p):
 t=canonical(t)
 if len(forms)>=MAX_FORMS or size(t)>MAX_SIZE or t in where:return
 if any(subsumes(forms[j],t) for j in active):return
 idx=len(forms); forms.append(t);parents.append(p);where[t]=idx
 active.difference_update(j for j in list(active) if subsumes(t,forms[j]))
 active.add(idx);heapq.heappush(heap,(size(t),idx))
 if t in targets:found[targets[t]]=idx;print('FOUND',targets[t],idx,flush=True)
for name,t in seeds:add(t,{'seed':name})
# Generalize a theorem schema using a genuinely new arbitrary numeric binder.
while heap and len(forms)<MAX_FORMS and attempts<MAX_ATTEMPTS and time.monotonic()-start<MAX_SECONDS:
 _,i=heapq.heappop(heap)
 if i not in active:continue
 add(Q(999,forms[i]),{'gen':i})
 for j in sorted((done&active)|{i},key=lambda j:size(forms[j])):
  for ma,mi in ((i,j),(j,i)) if i!=j else ((i,i),):
   attempts+=1;r=detach(forms[ma],forms[mi])
   if r is not None:add(r[0],{'major':ma,'minor':mi,'substitution':list(r[1].items())})
   if len(forms)>=MAX_FORMS or attempts>=MAX_ATTEMPTS or time.monotonic()-start>=MAX_SECONDS:break
  if len(forms)>=MAX_FORMS or attempts>=MAX_ATTEMPTS or time.monotonic()-start>=MAX_SECONDS:break
 done.add(i)
report={'bounds':{'forms':MAX_FORMS,'attempts':MAX_ATTEMPTS,'term_size':MAX_SIZE,'seconds':MAX_SECONDS},
 'actual':{'forms':len(forms),'attempts':attempts,'active':len(active),'processed':len(done),'seconds':time.monotonic()-start},
 'found':found,'scope':'Exact native universal logical schemas H_B and H_Rbc plus rho1-rho6/G/truth/GEN/MP; no bundle seed or projection is assumed. A negative result does not establish full-seed consistency or rule out a bootstrap.','received_code_executed':False,'nodes':[{'id':i,'term':t,'parent':parents[i]} for i,t in enumerate(forms)]}
(OUT/'BOUNDED_HB_RBC_RESULT.json').write_text(json.dumps(report,indent=2))
print(json.dumps({k:v for k,v in report.items() if k!='nodes'},indent=2))
