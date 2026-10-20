#!/usr/bin/env python3
"""Bounded sound constructor-schema detachment, with no assumed substitution rule.
Each retained schema is universal in its numerical metavariables. Witnesses
record the two disjoint instantiations. Search is incomplete, including occurs
checks that reject some possible native-zero solutions.
"""
from pathlib import Path
import json,time,hashlib
T=('T',)
def I(a,b):return T if a==T and b==T else ('I',a,b)
def R(a,b):return ('R',a,b)
def Q(a,b):return ('Q',a,b)
def E(a,b):return ('E',a,b)
F=R(T,T)
def N(x):return I(x,F)
def Ex(i,x):return N(Q(i,N(x)))
def var(i):return ('v',i)
a,b,c=map(var,range(3))
K=I(a,I(b,a));H=I(I(I(c,F),a),I(I(a,c),I(b,c)))
def norm(x,s):
 if x[0]=='v' and x[1] in s:return norm(s[x[1]],s)
 if x[0]=='I':return I(norm(x[1],s),norm(x[2],s))
 if x[0] in ('R','Q','E'):return (x[0],norm(x[1],s),norm(x[2],s))
 return x
def occ(v,x):return x==var(v) or (len(x)==3 and (occ(v,x[1]) or occ(v,x[2])))
def unify(a,b,s):
 a,b=norm(a,s),norm(b,s)
 if a==b:return True
 if a[0]=='v':
  if occ(a[1],b):return False
  s[a[1]]=b;return True
 if b[0]=='v':return unify(b,a,s)
 if a==T and b[0]=='I':return unify(b[1],T,s) and unify(b[2],T,s)
 if b==T and a[0]=='I':return unify(a[1],T,s) and unify(a[2],T,s)
 if a[0]!=b[0] or len(a)!=3:return False
 return unify(a[1],b[1],s) and unify(a[2],b[2],s)
def rename(x,off):
 if x[0]=='v':return var(x[1]+off)
 if len(x)==3:return (x[0],rename(x[1],off),rename(x[2],off))
 return x
def canon(x):
 d={}
 def f(y):
  if y[0]=='v':return var(d.setdefault(y[1],len(d)))
  if len(y)==3:return(y[0],f(y[1]),f(y[2]))
  return y
 return f(x)
def size(x):return 1+size(x[1])+size(x[2]) if len(x)==3 else 1
p=Path(__file__).resolve().parent;start=time.monotonic();nodes=[];known={};queue=[];pairs=0
MAX=2500;SIZE=55;LIMIT=15
axioms=[('truth',T),('EFQ',I(F,a)),('restricted_rho8_F',H),('rho1',Ex(a,E(a,b))),('rho2',I(Q(a,I(b,c)),I(Q(a,b),Q(a,c)))),('rho3',I(E(a,b),I(R(c,a),R(c,b)))),('rho4',I(Q(a,Q(b,c)),Q(b,Q(a,c)))),('rho5',I(E(c,a),I(R(c,b),R(a,b)))),('rho6',I(Ex(a,Q(a,b)),b)),('G',I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b)))))]
for label,x in axioms:known[x]=len(nodes);nodes.append({'formula':x,'rule':label});queue.append(x)
targets={'identity':I(a,a),'K':K,'S':I(I(a,I(b,c)),I(I(a,b),I(a,c))),'Peirce':I(I(I(a,b),a),a),'DNE':I(N(N(a)),a),'QS':I(N(N(Q(a,b))),Q(a,b))};found={};cursor=0
while cursor<len(nodes) and len(nodes)<MAX and time.monotonic()-start<LIMIT:
 n=len(nodes)
 g=canon(Q(var(999),nodes[cursor]['formula']))
 if size(g)<=SIZE and g not in known:
  known[g]=len(nodes);nodes.append({'formula':g,'rule':'gen','parent':cursor,'label':var(999)})
 for i,j in [(cursor,j) for j in range(n)]+[(i,cursor) for i in range(cursor)]:
  major=nodes[i]['formula'];minor=rename(nodes[j]['formula'],1000);pairs+=1
  if major[0]!='I':continue
  sub={}
  if not unify(major[1],minor,sub):continue
  before=norm(major,sub);used=norm(minor,sub)
  if before==T:
   assert used==T
   goal=T
  else:
   assert before[0]=='I' and before[1]==used
   goal=canon(before[2])
  if size(goal)>SIZE or goal in known:continue
  known[goal]=len(nodes);nodes.append({'formula':goal,'rule':'condensed_mp','major':i,'minor':j,'minor_rename_offset':1000,'substitution':sub,'instantiated_major':before,'instantiated_minor':used});queue.append(goal)
  for label,target in targets.items():
   if goal==target and label not in found:found[label]=len(nodes)-1;print('FOUND',label,found[label],flush=True)
  if len(nodes)>=MAX or time.monotonic()-start>=LIMIT:break
 cursor+=1
result={'status':'BOUNDED_SCHEMATIC_SEARCH_COMPLETE','seconds':time.monotonic()-start,'nodes':len(nodes),'processed':cursor,'pairs':pairs,'max_nodes':MAX,'max_term_size':SIZE,'seconds_cap':LIMIT,'found':found,'scope':'Truth, explicit EFQ, restricted F row, rho1-6, G, theorem-only GEN and actual MP instantiation. Gated bundle omitted, not weakened. No free renaming/substitution rule. Missing targets establish no unprovability result.'}
(p/'modal-proof.json').write_text(json.dumps(nodes,separators=(',',':'))+'\n');(p/'modal-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
