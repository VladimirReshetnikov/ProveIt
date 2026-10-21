"""Owned bounded literal prefix contract evaluator, independent of row-plan code."""
import time,collections
class Budget(Exception):pass
class PrefixFailure(Exception):pass
class Counter:
 def __init__(self,steps,seconds):self.maximum=steps;self.deadline=time.monotonic()+seconds;self.steps=0
 def tick(self):
  if self.steps>=self.maximum or time.monotonic()>=self.deadline:raise Budget('prefix budget exhausted')
  self.steps+=1

def allocate(table,root,counter):
 groups=collections.defaultdict(set);paths={};gates=[]
 def leaf(n):return isinstance(n[0],str)
 def visit(n,p):
  if leaf(n):return
  tape={-1:1,**{i:int(b)for i,b in enumerate(p)}};initial=tape.copy();q=84;h=0;seen=set();trace=[]
  while h!=len(p):
   if q==254 or h not in tape:raise PrefixFailure(('unknown prefix',p,q,h,trace[-12:]))
   key=q,h,tuple(tape.values())
   if key in seen:raise PrefixFailure(('cycle',p,q,h,trace[-12:]))
   seen.add(key);counter.tick();b=tape[h];w,d,z=table[q,b];trace.append([q,h,b,w,d,z]);tape[h]=w;h+=d;q=z
  if tape!=initial:raise PrefixFailure(('dirty prefix',p,q,trace[-12:]))
  groups[q].add(n);paths[p]=q
  for b,ch in enumerate(n):
   if leaf(ch):gates.append((ch,b,table[q,b],p+str(b)))
   else:visit(ch,p+str(b))
 visit(root,'');return groups,paths,gates
