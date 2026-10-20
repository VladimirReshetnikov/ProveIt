"""Hash-consed source DAG used by the bounded rotation search."""
import functools
from model import leaf
class Dag:
 def __init__(self):self.ns=[];self.ids={};self.br=[];self.co=[];self.lead=[];self.zero=[]
 def add(self,n):
  if n in self.ids:return self.ids[n]
  q=len(self.ns);self.ns.append(n);self.ids[n]=q
  if isinstance(n[0],str):
   op,a=n;self.br.append(1 if op=='CD' else a if op=='CB' else 0);self.co.append(a if op=='CC' else 0);self.lead.append(0);self.zero.append(0)
  else:
   a,b=n;self.br.append(max(self.br[a]-1,self.br[b],0));self.co.append(max(self.co[a],self.co[b]-1,0));self.lead.append(1+self.lead[a]);self.zero.append(max(1+self.lead[a],self.zero[a],self.zero[b]))
  return q
 def intern(self,t):return self.add(t if leaf(t) else (self.intern(t[0]),self.intern(t[1])))
 def reach(self,r):
  seen=set();todo=[r]
  while todo:
   q=todo.pop()
   if q in seen:continue
   seen.add(q)
   if not isinstance(self.ns[q][0],str):todo.extend(self.ns[q])
  return seen
 def replace(self,r,x,y):
  @functools.lru_cache(None)
  def rec(q):
   if q==x:return y
   n=self.ns[q]
   return q if isinstance(n[0],str) else self.add((rec(n[0]),rec(n[1])))
  return rec(r)
 def tree(self,r):
  @functools.lru_cache(None)
  def rec(q):
   n=self.ns[q];return n if isinstance(n[0],str) else (rec(n[0]),rec(n[1]))
  return rec(r)
