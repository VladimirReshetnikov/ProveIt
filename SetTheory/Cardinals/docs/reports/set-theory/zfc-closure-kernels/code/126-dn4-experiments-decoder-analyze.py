from pathlib import Path
import sys,json,collections,os
P=Path(os.environ['ZFC_BASELINE_PORTABLE']).resolve()
assert (P/'results/candidate225.klabels.tm').is_file(), 'ZFC_BASELINE_PORTABLE must name the retained K225 portable directory'
sys.path.insert(0,str(P/'baseline226/verification'));import reconstruct227 as c
sys.path.insert(0,str(P/'tools'));import verify_state_fold as v
t,start=v.parse_table((P/'results/candidate225.klabels.tm').read_bytes())
root=c.tree(json.loads((P/'results/sites225.json').read_text()))
def mapping(t,root):
 qs=collections.defaultdict(set);paths=collections.defaultdict(list);nodeq=collections.defaultdict(set);leafs=collections.defaultdict(set)
 def walk(n,p,q):
  if c.leaf(n):leafs[n].add(q);return
  qs[q].add(n);paths[q].append(p);nodeq[n].add(q)
  for b in (0,1):
   if c.leaf(n[b]):continue
   mem={i:int(x) for i,x in enumerate(p+str(b))};mem[-1]=1;orig=mem.copy();h=len(p);state=q
   for k in range(100):
    if h==len(p)+1:break
    c.require(h in mem,'decoder outside known path')
    w,d,state=t[state,mem[h]];mem[h]=w;h+=d
   c.require(mem==orig and h==len(p)+1,'prefix decoder mismatch')
   walk(n[b],p+str(b),state)
 walk(root,'',84)
 return qs,paths,nodeq,leafs
if __name__=='__main__':
 qs,paths,nodeq,leafs=mapping(t,root)
 facts,checks=v.bit_invariant(t,0,8)
 print('metrics',c.metrics(root),'decoder states',len(qs))
 print('leafs',dict(leafs))
 print('multi node',[(q,len(ns),len(paths[q]))for q,ns in qs.items()if len(ns)>1])
 print('nonpure',[(q,t[q,0],t[q,1],facts[q])for q in qs if any(t[q,b][:2]!=(b,1)for b in(0,1))])
 print('six zero sites',sum('000000' in p for p,op,arg in c.sites(root)))
 seen=set()
 for p,op,arg in c.sites(root):
  if '000000' not in p:continue
  pre=p[:p.index('000000')]
  n=c.subtree(root,pre)
  if n in seen:continue
  seen.add(n)
  print('six root',pre,'q',nodeq[n],'length',len(c.sites(n)),'boundary',c.boundary(n))
  for i in range(1,7):
   k=c.subtree(n,'0'*i)
   print('child',i,'q',nodeq[k],'size',len(c.sites(k)),'boundary',c.boundary(k))
