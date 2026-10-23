"""Authored hash-consed polynomial circuits with exact binary operation counts."""
class Circuit:
 def __init__(self):self.nodes=[];self.cache={};self.powers={};self.names={}
 def node(self,kind,*args):
  if kind in ('add','mul'):args=tuple(sorted(args))
  key=(kind,)+args
  if key not in self.cache:
   self.cache[key]=len(self.nodes)
   self.nodes.append(dict(kind=kind,**({'left':args[0],'right':args[1]} if kind in ('add','sub','mul') else {'value' if kind=='literal' else 'name':args[0]})))
  return self.cache[key]
 def c(self,n):return self.node('literal',n)
 def op(self,k,a,b):
  x=self.nodes[a].get('value');y=self.nodes[b].get('value')
  if x is not None and y is not None:return self.c(x+y if k=='add' else x-y if k=='sub' else x*y)
  if k=='add' and x==0:return b
  if k in ('add','sub') and y==0:return a
  if k=='mul':
   if x==0 or y==0:return self.c(0)
   if x==1:return b
   if y==1:return a
  return self.node(k,a,b)
 def add(self,*args):
  t=self.c(0)
  for x in args:t=self.op('add',t,x)
  return t
 def mul(self,*args):
  t=self.c(1)
  for x in args:t=self.op('mul',t,x)
  return t
 def sub(self,a,b):return self.op('sub',a,b)
 def pow(self,a,k):
  if k==0:return self.c(1)
  if k==1:return a
  if (a,k) not in self.powers:
   t=self.pow(a,k//2);t=self.mul(t,t)
   self.powers[a,k]=self.mul(t,a) if k%2 else t
  return self.powers[a,k]
 def geom(self,a,k):
  if k==0:return self.c(0)
  if k==1:return self.c(1)
  t=self.mul(self.geom(a,k//2),self.add(self.c(1),self.pow(a,k//2)))
  return self.add(t,self.pow(a,k-1)) if k%2 else t
 def save(self,name,t):self.names[name]=t;return t
 def export(self,out):
  used=set();todo=[out]
  while todo:
   i=todo.pop()
   if i in used:continue
   used.add(i);n=self.nodes[i]
   if 'left'in n:todo += [n['left'],n['right']]
  remap={i:j for j,i in enumerate(sorted(used))};ns=[]
  for i in sorted(used):
   n=dict(self.nodes[i])
   if 'left'in n:n['left']=remap[n['left']];n['right']=remap[n['right']]
   ns.append(n)
  return ns,remap[out],{n:remap[i] for n,i in self.names.items() if i in remap}
