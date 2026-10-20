"""Independent source CFG from complete-trie intervals and ancestor unwinding."""
import hashlib
def need(v,m):
 if not v:raise ValueError(m)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def cfg(rows):
 ordered=sorted(rows);term={}
 need(len(rows)==4744,'source length')
 for i,(p,op,a)in enumerate(ordered):
  need(type(p)is str and p and set(p)<=set('01')and p not in term,'path');term[p]=i
 prefixes={p[:k]for p in term for k in range(len(p))};need(not(set(term)&prefixes),'prefix-free');nodes=prefixes|set(term)
 for p in prefixes:need(p+'0'in nodes and p+'1'in nodes,'full trie')
 intervals={}
 def visit(p):
  if p in term:lo=hi=term[p]
  else:
   l,r=visit(p+'0'),visit(p+'1');need(l[1]+1==r[0],'interval ordering');lo,hi=l[0],r[1]
  intervals[p]=(lo,hi);return lo,hi
 visit('');n=len(rows)
 def ancestor(p,c,k):
  if k==0:return p
  for j in range(len(p)-1,-1,-1):
   if p[j]==c:
    k-=1
    if k==0:return p[:j]
  return ''
 def br(p,k):return(intervals[ancestor(p,'0',k)][1]+1)%n
 def co(p,k):return intervals[ancestor(p,'1',k)][0]
 G=[]
 for i,(p,op,a)in enumerate(ordered):
  if op in('CI','CD'):
   need(type(a)is int and 0<=a<9,'register');G.append(['INC',a,(i+1)%n]if op=='CI'else['DEC',a,(i+1)%n,br(p,1)])
  elif op in('CB','CC'):
   need(type(a)is int and a>=0,'jump');G.append(['JUMP',br(p,a)if op=='CB'else co(p,a)])
  else:need(op=='CH'and a is None,'halt');G.append(['HALT'])
 return ordered,G,intervals[''][0]
