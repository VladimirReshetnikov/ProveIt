from invariant_search import *
import source_language as s
from functools import cache
S=json.loads((BASE/'machine/sites221.json').read_text());TREE=s.tree(S)
@cache
def touches(n):
 if s.leaf(n):return frozenset([n[1]])if n[0]in('CI','CD')else frozenset()
 return touches(n[0])|touches(n[1])
@cache
def leaves(n):return 1 if s.leaf(n)else leaves(n[0])+leaves(n[1])
@cache
def nodes(n):return frozenset([n])if s.leaf(n)else frozenset([n])|nodes(n[0])|nodes(n[1])
@cache
def subst(n,x,y):
 if n==x:return y
 if s.leaf(n):return n
 return subst(n[0],x,y),subst(n[1],x,y)
found=[]
for n in nodes(TREE):
 if s.leaf(n):continue
 a,b=n
 if s.boundary(a)==s.boundary(b)==(0,0,False)and not(touches(a)&touches(b))and a!=b:
  out=subst(TREE,n,(b,a));m=s.metrics(out)
  rec={'size':leaves(n),'touch_a':sorted(touches(a)),'touch_b':sorted(touches(b)),'dag':m['dag_nodes'],'zero':m['maximum_zero_run'],'node':n}
  found.append(rec);print(rec if leaves(n)<12 else {k:v for k,v in rec.items()if k!='node'})
Path('commute_block_results.json').write_text(json.dumps(found,indent=2));print('COUNT',len(found))
