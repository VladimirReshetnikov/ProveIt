import itertools,time,json

def parse(s):
 it=iter(s)
 def rec():
  x=next(it)
  return (rec(),rec()) if x=='C' else ord(x)-ord('p')
 a=rec(); assert list(it)==[];return canon(a)
def canon(t):
 d={}
 def f(x):
  if isinstance(x,int):
   if x not in d:d[x]=len(d)
   return d[x]
  return tuple(map(f,x))
 return f(t)
def shift(t):return t+100 if isinstance(t,int) else tuple(map(shift,t))
def size(t):return 0 if isinstance(t,int) else 1+size(t[0])+size(t[1])
def fmt(t):return chr(112+t) if isinstance(t,int) else 'C'+fmt(t[0])+fmt(t[1])
def cd(a,b):
 if isinstance(a,int):return None
 b=shift(b);sub={};stack=[(a[0],b)]
 def walk(x):
  while isinstance(x,int) and x in sub:x=sub[x]
  return x
 def occurs(k,t):
  t=walk(t)
  return k==t if isinstance(t,int) else occurs(k,t[0]) or occurs(k,t[1])
 def inst(t):
  t=walk(t)
  return t if isinstance(t,int) else tuple(map(inst,t))
 while stack:
  x,y=map(walk,stack.pop())
  if x==y:continue
  if isinstance(x,int):
   if occurs(x,y):return None
   sub[x]=y
  elif isinstance(y,int):
   if occurs(y,x):return None
   sub[y]=x
  else:stack.extend(zip(x,y))
 return canon(inst(a[1]))
def subsumes(a,b):
 m={};st=[(a,b)]
 while st:
  x,y=st.pop()
  if isinstance(x,int):
   if x in m:
    if m[x]!=y:return False
   else:m[x]=y
  elif isinstance(y,int):return False
  else:st.extend(zip(x,y))
 return True

A=[parse('CpCqp'),parse('CCCpqrCCrpCqp')]; proofs=[None,None];goals=[parse('CpCqp'),parse('CCCpqpp'),parse('CCpCqrCCpqCpr')];found={};maxsize=10
start=time.time();k=0
while k<len(A) and k<10000 and time.time()-start<180:
 for j in range(k+1):
  for x,y in [(k,j),(j,k)]:
   r=cd(A[x],A[y])
   if r is None or size(r)>maxsize:continue
   if any(subsumes(t,r) for t in A):continue
   idx=len(A);A.append(r);proofs.append((x,y))
   for gi,g in enumerate(goals):
    if gi not in found and subsumes(r,g):
     found[gi]=idx;print('FOUND',gi,idx,fmt(r),'step',k,flush=True)
   if len(found)>=2:break
  if len(found)>=2:break
 if len(found)>=2:break
 if k%50==0:print('PROGRESS',k,len(A),time.time()-start,flush=True)
 k+=1
ids=set()
def anc(i):
 if i in ids:return
 ids.add(i)
 if proofs[i]:
  for j in proofs[i]:anc(j)
for i in found.values():anc(i)
for i in sorted(ids):print(i,fmt(A[i]),proofs[i])
print('END',k,len(A),found,time.time()-start)
json.dump({'formulae':[fmt(t) for t in A],'proofs':proofs,'found':found},open('research217_three_variable_axioms/k_lq_search.json','w'))
