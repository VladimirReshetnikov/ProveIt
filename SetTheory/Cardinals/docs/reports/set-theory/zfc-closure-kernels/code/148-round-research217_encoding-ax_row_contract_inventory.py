"""Owned analytic binding of the current205 source AX emitters. No permutations searched."""
from pathlib import Path
from functools import lru_cache
import sys,json,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'research218_published_encoding'));import audit_construction as A
sites=json.load(open(A.NEW/'sites218.json'));tree=A.P.tree(sites);T=A.R.table(A.NEW/'k218.native.tm');groups,paths,gates=A.P.allocation(T,tree)
@lru_cache(None)
def flat(n):return(n,)if A.P.leaf(n)else flat(n[0])+flat(n[1])
def sole(q):assert len(groups[q])==1;return next(iter(groups[q]))
def serial(xs):
 n=xs[-1]
 for x in reversed(xs[:-1]):n=x,n
 return n
inc=('CI',1);I=sole(90);N=sole(184)
macros={'a':sole(98),'b':sole(12),'c':sole(166),'1':N[0],'I':I,'N':N,'Q':(I,(inc,inc)),'R':(I,inc),'E':(I,((inc,inc),inc))}
macros['X']=(N,(macros['Q'],N))
assert all(A.boundary(m)==(0,0,False)for m in macros.values())
intervals={'rho8':(135,486),'G':(486,895),'rho6':(895,1178),'rho5':(1178,1474),'rho4':(1474,1773),'rho3':(1773,2069),'rho2':(2069,2419),'rho1':(2419,2650)}
words={'rho8':['c','u','I','a','I','a','c','I','b','c','I','I','I'],'G':['c','a','E','c','b','E','a','b','R','a','b','E','Q','I','I'],'rho6':['a','a','c','Q','X','c','I'],'rho5':['c','a','E','c','b','R','a','b','R','I','I'],'rho4':['a','b','c','Q','Q','b','a','c','Q','Q','I'],'rho3':['a','b','E','c','a','R','c','b','R','I','I'],'rho2':['a','b','c','I','Q','a','b','Q','a','c','Q','I','I'],'rho1':['a','a','b','E','X']}
# Rebuild exactly the two closed pieces of the fourth-field load.
def cover(lo,hi):
 result=[]
 def walk(n,i,p):
  j=i+A.length(n)
  if j<=lo or hi<=i:return
  if lo<=i and j<=hi and A.boundary(n)==(0,0,False):result.append((i,j,p,n));return
  assert not A.P.leaf(n);walk(n[0],i,p+'0');walk(n[1],i+A.length(n[0]),p+'1')
 walk(tree,0,'');assert sum(j-i for i,j,p,n in result)==hi-lo;return result
readerparts=cover(161,194);macros['u']=serial([n for i,j,p,n in readerparts]);assert A.boundary(macros['u'])==(0,0,False)
assert macros['a'][0]==macros['b'][0]==macros['c'][0]==readerparts[0][3] and A.length(readerparts[0][3])==19
assert flat(macros['u'])==tuple(tuple(x[1:])for x in sites[161:194])
# Closed-local CFG with a distinct end sentinel, so back-edge0 is not confused with exit.
def localcfg(t):
 out=[];size=A.length(t)
 def walk(n,i,breaks,continues):
  if A.P.leaf(n):
   op,k=n
   def get(st,k):assert len(st)>=k;return st[-k]
   edges=[]if op=='CH'else[get(continues,k)]if op=='CC'else[get(breaks,k)]if op=='CB'else[get(breaks,1),i+1]if op=='CD'else[i+1]
   assert len(out)==i;out.append([op,None if op in('CB','CC')else k,edges]);return
  m=i+A.length(n[0]);j=i+A.length(n);walk(n[0],i,breaks+[j],continues);walk(n[1],m,breaks,continues+[i])
 walk(t,0,[],[]);assert all(0<=e<=size for row in out for e in row[2]);return out
G=A.continuation_cfg(tree);assert G==A.address_cfg(sites)
assert flat(macros['a'])==tuple(tuple(s[1:])for s in sites[2650:2676])
assert localcfg(macros['a'])==[[op,k,[e-2650 for e in es]]for op,k,es in G[2650:2676]]
F=lambda op,a,b:[op,a,b]
def formula(word):
 st=[]
 for op in word:
  if op in('a','b','c','u','1'):st.append(op if op!='1' else 1)
  elif op=='N':st.append(F('I',st.pop(),1))
  else:
   b=st.pop();a=st.pop();st.append(F('I',F('Q',a,F('I',b,1)),1)if op=='X'else F(op,a,b))
 assert len(st)==1;return st[0]
reports=[]
for name,(lo,hi)in intervals.items():
 t=serial([macros[c]for c in words[name]]);assert A.boundary(t)==(0,0,False)
 assert flat(t)==tuple(tuple(s[1:])for s in sites[lo:hi])
 actual=[[op,k,[e-lo for e in edges]]for op,k,edges in G[lo:hi]];assert localcfg(t)==actual
 for i,row in enumerate(G):
  if not lo<=i<hi:assert all(not lo<e<hi for e in row[2]),('external interior entry',name,i,row)
 reports.append(dict(name=name,interval=[lo,hi],leaves=hi-lo,macro_word=words[name],emitted_formula=formula(words[name]),literal_primitive_word_and_all_guarded_internal_edges_match=True,only_entry_at_beginning=True,only_exit_at_end=True,parameter_registers_preserved=[3,4,5],scratch_zero_at_boundaries=[6,7],changes_prooflist_only=name=='rho8'))
# Locate indivisible closed atoms in the CURRENT source, with unchanged outer tree.
atoms=[]
def template(n,i=0,p=''):
 j=i+A.length(n)
 if j<=135 or i>=2650:return ['F',p]
 if 135<=i and j<=2650 and A.boundary(n)==(0,0,False) and(A.P.leaf(n)or any(A.boundary(c)!=(0,0,False)for c in n)):
  k=len(atoms);atoms.append(dict(interval=[i,j],path=p,tree=n));return['A',k]
 assert not A.P.leaf(n);return['N',template(n[0],i,p+'0'),template(n[1],i+A.length(n[0]),p+'1')]
tpl=template(tree);rowatoms={}
for name,(lo,hi)in intervals.items():
 ids=[k for k,a in enumerate(atoms)if lo<=a['interval'][0]and a['interval'][1]<=hi];assert sum(atoms[k]['interval'][1]-atoms[k]['interval'][0]for k in ids)==hi-lo;rowatoms[name]=ids
assert sum(map(len,rowatoms.values()))==len(atoms)
oldreceipt=ROOT/'latest219_baseline/source138/research/encoding/receipts/row_order_atoms_summary.json';prior=json.load(open(oldreceipt))
out=dict(status='CURRENT205_EMITTER_BINDING_PASS_NO_SEARCH',source_sha256=A.H(A.NEW/'sites218.json'),table_sha256=A.H(A.NEW/'k218.native.tm'),source_nodes=205,prior_received_receipt=dict(file=str(oldreceipt.relative_to(ROOT)),sha256=A.H(oldreceipt),status=prior['status'],row_orders=prior['row_orders'],minimum_dag_nodes=prior['minimum_dag_nodes'],baseline='K221/source208, not current205; inert receipt only, not independently rerun'),rows=reports,reader_parts=[dict(interval=[i,j],path=p,leaves=j-i)for i,j,p,n in readerparts],reader_contract='Input arbitrary R1=t,R2=s,R8=P(u,v), R6=R7=0. Output R1=u,R2=P(t,s),R8=v,R6=R7=0. R0,R3,R4,R5 unchanged. Thus it is a fourth-field push, safe to move intact with rho8 past other row emitters.',parameter_mapping={'a':4,'b':5,'c':3},row_atoms=rowatoms,atoms=atoms,template=tpl,possible_adjacent_swaps=list(zip(list(intervals)[:-1],list(intervals)[1:])),initial_interior_swaps=list(zip(list(intervals)[1:-2],list(intervals)[2:-1])),scope='All-natural macro composition is justified in accompanying proof; complete row permutation changes stack positions and requires compiler offset remapping. No physical allocation, permutation cost census or new calibrated binary machine is claimed.')
(OUT/'AX_ROW_CONTRACT_INVENTORY.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in('rows','atoms','template','row_atoms')},indent=2));print('atoms',len(atoms),'row counts',{k:len(v)for k,v in rowatoms.items()})
