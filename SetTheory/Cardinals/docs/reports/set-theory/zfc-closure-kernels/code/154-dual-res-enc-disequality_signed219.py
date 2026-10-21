#!/usr/bin/env python3
"""Signed logical rows for disequality coding, with exact surrounding CFG repair."""
import itertools,json,time
from pathlib import Path
import inverse_mp as q
import recompile219 as compiler
import closed_parse as cp
s,b,z=q.s,q.b,q.z
BASE=q.W/'K219_Construction_2026-10-20'
ROWS=json.loads((BASE/'machine/sites219.json').read_text());OLD=s.tree(ROWS)
OLDG=s.graph_intervals(ROWS);T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
OUT=q.W/'disequality_signed219';OUT.mkdir(exist_ok=True)
I=lambda a,b:('I',a,b)
R=lambda a,b:('R',a,b)
J=lambda a,b:('J',a,b)
Q=lambda a,b:('Q',a,b)
N=lambda a:('N',a)
X=lambda a,b:('X',a,b)
a,bb,c='a','b','c'
vars={'a':166,'b':121,'c':168}
def emit(n):
 if isinstance(n,str):return[vars[n]]
 if n[0]=='N':return emit(n[1])+[218]
 return emit(n[1])+emit(n[2])+[{'I':119,'R':181,'J':182,'Q':180,'X':183}[n[0]]]
rhs3=[I(N(J(a,bb)),I(R(c,a),R(c,bb))),
      I(R(c,a),I(N(R(c,bb)),J(a,bb))),
      I(N(R(c,bb)),I(R(c,a),J(a,bb)))]
rhs5=[I(N(J(c,a)),I(R(c,bb),R(a,bb))),
      I(R(c,bb),I(N(R(a,bb)),J(c,a))),
      I(N(R(a,bb)),I(R(c,bb),J(c,a)))]
ex=X(R(a,bb),J(a,bb))
gs=[I(N(J(c,a)),I(N(J(c,bb)),Q(R(a,bb),N(J(a,bb))))),
    I(ex,I(N(J(c,a)),J(c,bb))),I(N(J(c,a)),I(ex,J(c,bb))),
    I(ex,I(N(J(c,bb)),J(c,a))),I(N(J(c,bb)),I(ex,J(c,a)))]
rho1=N(Q(a,J(a,bb)))
intervals={'G':(486,895),'rho5':(1178,1474),'rho3':(1773,2069),'rho1':(2419,2650),'NIP':(4598,4610)}
odd=(('CD',5),((('CD',5),('CC',2)),('CH',None)))
E=s.subtree(OLD,'111110')
def swap(n):
 if s.leaf(n):
  op,arg=n
  return(op,11-arg)if op in('CI','CD')and arg in(5,6)else n
 return swap(n[0]),swap(n[1])
def eqswap(n):
 if n==E:return swap(n)
 if s.leaf(n):return n
 return eqswap(n[0]),eqswap(n[1])

def splice(replacements):
 cursor=0;origins=[];row_starts={};row_ends={};taken={}
 for name,(lo,hi)in intervals.items():
  for i in range(lo,hi):taken[i]=name
 def go(n):
  nonlocal cursor
  if s.leaf(n):
   i=cursor;cursor+=1
   name=taken.get(i)
   if name is None:origins.append(('old',i));return n
   if i!=intervals[name][0]:return None
   row_starts[name]=len(origins)
   repl=replacements[name];origins.extend((name,j)for j in range(len(s.sites(repl))))
   row_ends[name]=len(origins);return repl
  l,r=go(n[0]),go(n[1])
  return r if l is None else l if r is None else(l,r)
 tree=go(OLD);rr=s.sites(tree);assert len(rr)==len(origins)
 oldmap={i:j for j,(typ,i)in enumerate(origins)if typ=='old'}
 def target(i):return row_starts[taken[i]]if i in taken else oldmap[i]
 local={name:s.graph_intervals(s.sites((n,('CH',None))))for name,n in replacements.items()}
 expected=[]
 for typ,i in origins:
  if typ=='old':
   effect,targets=OLDG[i]
   for j in targets:
    assert j not in taken or j==intervals[taken[j]][0],('external_entry_inside_row',i,j,taken.get(j))
   expected.append([effect,[target(j)for j in targets]])
  else:
   effect,targets=local[typ][i];start=row_starts[typ]
   expected.append([effect,[(start+j)%len(rr)for j in targets]])
 # The opcode effects remain fixed. Relevel explicit control primitives to
 # their exact intended ordinal edge; conditional-decrement scopes must match.
 trial=s.graph_intervals(rr)
 for idx,(row,want,actual)in enumerate(zip(rr,expected,trial)):
  if actual==want:continue
  path,op,arg=row
  if op not in('CB','CC'):raise ValueError(('changed_noncontrol_edge',idx,row,actual,want))
  choices=[]
  for k in range(1,len(path)+2):
   row[2]=k
   if s.graph_intervals(rr)[idx]==want:choices.append(k)
  if not choices:raise ValueError(('missing_control_depth',idx,want))
  row[2]=arg if arg in choices else min(choices)
 assert s.graph_arithmetic(rr)[0]==s.graph_intervals(rr)==expected
 tree=s.tree(rr)
 paths={name:q.x.at_interval(tree,row_starts[name],row_ends[name])for name in replacements}
 return tree,paths

results=[];best=999;start=time.time()
for gi,ri,si in itertools.product(range(5),range(3),range(3)):
 words={'G':emit(gs[gi]),'rho5':emit(rhs5[si]),'rho3':emit(rhs3[ri]),'rho1':emit(rho1)}
 repl={name:z.seq([z.MACRO[m]for m in word])for name,word in words.items()};repl['NIP']=odd
 name=f'g{gi}_r3{ri}_r5{si}';rec={'name':name,'words':words}
 try:tree,paths=splice(repl)
 except Exception as exc:rec['splice_error']=repr(exc);results.append(rec);print(json.dumps(rec),flush=True);continue
 for seed in range(3):
  tr=tree
  try:
   for field in ['G','rho5','rho3','rho1']:
    tr,_=cp.parse_one(tr,OLD,paths[field],6,seed)
  except Exception as exc:rec['parse_error']=repr(exc);continue
  for eswap in [False,True]:
   tt=eqswap(tr)if eswap else tr;metric=s.metrics(tt)
   item={**rec,'seed':seed,'swap_equality_counters':eswap,'metrics':metric}
   if metric['dag_nodes']<best:
    best=metric['dag_nodes'];print('BEST',best,name,seed,eswap,flush=True)
   if metric['dag_nodes']<=209:
    d=OUT/(name+f'_s{seed}'+('_swap'if eswap else''));d.mkdir(exist_ok=True)
    (d/'sites.json').write_bytes(s.compact(s.sites(tt)))
    try:
     U,meta=compiler.compile_tree(T,OLD,tt,extend_direct=True);item['compiler']=meta
     (d/'candidate.tm').write_bytes(b.table_bytes(U))
    except Exception as exc:item['compile_error']=repr(exc)
    (d/'receipt.json').write_text(json.dumps(item,indent=2)+'\n')
   results.append(item)
  print(name,'seed',seed,'DAG',metric['dag_nodes'],'elapsed',round(time.time()-start,2),flush=True)
payload={'best_DAG':best,'results':results,'seconds':time.time()-start,'scope':'Finite source grammar and decoder counts; runtime proof separate'}
(OUT/'summary.json').write_text(json.dumps(payload,indent=2)+'\n')
