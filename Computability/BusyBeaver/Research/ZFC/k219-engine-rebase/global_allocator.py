#!/usr/bin/env python3
"""Global retired pure-decoder pool, separate from same-position origin reuse.

The pool criterion is syntactic and recorded for each state. Allocation is
exploratory: decoder binding alone does not prove arithmetic leaf contracts.
"""
from collections import defaultdict,Counter
import hashlib
def need(x,m):
 if not x:raise ValueError(m)
def node_id(n):return hashlib.sha256(repr(n).encode()).hexdigest()
def compile_tree(s,b,table,old_src,new_src,*,hypothetical_entries=False,require_pure_rows=True):
 groups,paths=b.decoder_map(table,old_src)
 old_states=defaultdict(set)
 for q,nodes in groups.items():
  for n in nodes:old_states[n].add(q)
 live=set()
 def visit(n):
  if s.leaf(n) or n in live:return
  live.add(n);visit(n[0]);visit(n[1])
 visit(new_src)
 incoming=defaultdict(list)
 for (p,bit),row in table.items():incoming[row[2]].append((p,bit,row))
 pool=[];certificates=[];exclusions=Counter()
 for q,nodes in sorted(groups.items()):
  if q in(0,84):exclusions['start_or_dispatch']+=1;continue
  if any(n in live for n in nodes):exclusions['role_still_live']+=1;continue
  if require_pure_rows and not all(table[q,bit][:2]==(bit,1) for bit in(0,1)):
   exclusions['non_pure_own_rows']+=1;continue
  reasons=[];witness=[]
  for p,bit,row in incoming[q]:
   roles=groups.get(p,set())
   valid=row==(bit,1,q) and bool(roles) and all(not s.leaf(n[bit]) and n[bit] in nodes for n in roles)
   if not valid:reasons.append([p,bit,list(row),'not direct internal-child edge for every predecessor role'])
   witness.append(dict(predecessor=p,bit=bit,row=list(row),predecessor_roles=sorted(node_id(n) for n in roles),all_roles_internal_child=valid))
  if reasons:exclusions['unsafe_incoming']+=1;continue
  need(bool(incoming[q]),'Unreached pool state')
  pool.append(q);certificates.append(dict(state=q,retired_roles=sorted(node_id(n) for n in nodes),old_rows=[list(table[q,bit])for bit in(0,1)],incoming=witness))
 mapped={n:min(qs)for n,qs in old_states.items()};mapped[new_src]=84
 need(not(set(pool)&{mapped[n]for n in live if n in mapped}),'Pool overlaps preserved role')
 compiled=dict(table);fresh=max(300,max(q for q,bit in table)+1);fresh0=fresh;nextpool=0;assignments=[]
 leaves={}
 for op in('CI','CD','CC','CB','CH'):
  for arg in([None]if op=='CH'else range(10)):
   ch=op,arg
   for bit in(0,1):
    choices=Counter(table[q,bit]for n,qs in old_states.items()for q in qs if n[bit]==ch)
    direct=[a for a in choices if a[:2]==(bit,1)]
    if len(direct)==1:leaves[ch,bit]=direct[0]
    elif ch==('CC',1)and bit==1:leaves[ch,bit]=(0,-1,1)
    elif ch==('CC',2)and bit==1:leaves[ch,bit]=(0,-1,16)
    elif ch==('CB',1)and bit==1:leaves[ch,bit]=(0,-1,40)
 if hypothetical_entries:
  leaves[('CI',5),1]=(1,1,63);leaves[('CI',6),1]=(1,1,13)
 def go(n):
  nonlocal fresh,nextpool
  if n in mapped:return mapped[n]
  if nextpool<len(pool):q=pool[nextpool];nextpool+=1;kind='certified_syntactic_pool'
  else:q=fresh;fresh+=1;kind='fresh'
  mapped[n]=q;assignments.append(dict(state=q,node=node_id(n),kind=kind))
  for bit,ch in enumerate(n):
   if not s.leaf(ch):compiled[q,bit]=(bit,1,go(ch))
   else:
    need((ch,bit)in leaves,('No generic leaf entry',ch,bit,q))
    compiled[q,bit]=leaves[ch,bit]
  return q
 for bit,ch in enumerate(new_src):compiled[84,bit]=(bit,1,go(ch))if not s.leaf(ch)else leaves[ch,bit]
 reach={0};todo=[0]
 for q in todo:
  for bit in(0,1):
   z=compiled[q,bit][2]
   if z!=254 and z not in reach:reach.add(z);todo.append(z)
 compiled={k:v for k,v in compiled.items()if k[0]in reach}
 gg,_=b.decoder_map(compiled,new_src)
 for q,nodes in gg.items():
  for n in nodes:
   permitted=old_states[n]if n in old_states and n!=new_src else{mapped[n]}
   need(q in permitted,('Node binding mismatch',q,sorted(permitted)))
 untouched={q for q,bit in table}-{84}-{x['state']for x in assignments}
 need(all(compiled[q,bit]==table[q,bit] for q in untouched if q in reach for bit in(0,1)),'Preserved state row changed')
 return compiled,dict(working_states=len(compiled)//2,pool_size=len(pool),pool_used=nextpool,fresh=fresh-fresh0,pool_certificates=certificates,pool_exclusions=dict(exclusions),assignments=assignments,require_pure_rows=require_pure_rows,retained_rows_unchanged=True,scope='Explicit syntactic incoming-edge certificates and exact decoder-prefix binding only; old context-sensitive retained entries and fresh generic leaves still require primitive-runtime verification.')
