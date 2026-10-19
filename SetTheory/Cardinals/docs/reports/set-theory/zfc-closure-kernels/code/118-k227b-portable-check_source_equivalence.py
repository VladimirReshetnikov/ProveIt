"""Independent literal-graph binding of the transfer-plus-one source induction.
All checks remain active under -O. This is an ordinary proof, not kernel code.
"""
from pathlib import Path
import json,hashlib
H=Path(__file__).resolve().parent;D=H/'loop_delayed228'
import argparse
ap=argparse.ArgumentParser();ap.add_argument('--output-dir',type=Path,required=True);args=ap.parse_args();OUT=args.output_dir;OUT.mkdir(parents=True,exist_ok=True)

def require(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
P=H/'upstream/K230/machine/sites230.json';ops={'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'};old=[]
for p,x in json.loads(P.read_text()):
 a=x.split();old.append((p,ops[a[0]],int(a[1])if len(a)>1 else None))
new=[tuple(x)for x in json.loads((D/'sites.json').read_text())];receipt=json.loads((D/'source_equivalence.json').read_text());roots=receipt['rewrite_roots'];require(len(roots)==4 and len(set(roots))==4,'rewrite roots')
expectedold=[('00','CD',6),('010','CI',5),('011','CC',2),('1','CI',5)];expectednew=[('0','CI',5),('10','CD',6),('11','CC',2)]
for root in roots:
 require([(p[len(root):],o,r)for p,o,r in old if p.startswith(root)]==expectedold,'old block syntax')
 require([(p[len(root):],o,r)for p,o,r in new if p.startswith(root)]==expectednew,'new block syntax')
require([x for x in old if not any(x[0].startswith(r)for r in roots)]==[x for x in new if not any(x[0].startswith(r)for r in roots)],'outside source changed')
def graph(rows):
 require(rows==sorted(rows),'source order');paths={p:i for i,(p,o,r)in enumerate(rows)};prefixes={p[:k]for p in paths for k in range(len(p))};mx=max(map(len,paths));require(not(set(paths)&prefixes),'prefix-free');require(all(p+b in paths or p+b in prefixes for p in prefixes for b in'01'),'full tree')
 def locate(p):
  word=p+'0'*mx
  for k in range(1,mx+1):
   if word[:k]in paths:require('1'not in p[k:],'noncanonical suffix');return paths[word[:k]]
  raise ValueError('unresolved target')
 def inc(p):return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b')if p else''
 def cut(p,c,n):
  if n==0:return p
  z=[i for i,b in enumerate(p)if b==c];return p[:z[-n]]if len(z)>=n else''
 out=[]
 for p,o,r in rows:
  if o=='CI':out.append(('INC',r,locate(inc(p))))
  elif o=='CD':out.append(('DEC',r,locate(inc(p)),locate(inc(cut(p,'0',1)))))
  elif o=='CB':out.append(('JUMP',locate(inc(cut(p,'0',r)))))
  elif o=='CC':out.append(('JUMP',locate(cut(p,'1',r))))
  elif o=='CH':out.append(('HALT',))
  else:raise ValueError('opcode')
 return out,locate('')
def quotient(rows,expected_graph):
 g,start=graph(rows);blocks=[];owner={}
 for root in roots:
  ids=[i for i,(p,o,r)in enumerate(rows)if p.startswith(root)];require(ids==list(range(ids[0],ids[-1]+1)),'interval');require(ids[-1]+1<len(rows),'exit exists');begin,end=ids[0],ids[-1]+1;loc=[]
  for i in ids:
   x=g[i];ts=x[2:]if x[0]in('INC','DEC')else x[1:]if x[0]=='JUMP'else();require(all(begin<=z<=end for z in ts),'escaping block');ys=tuple(z-begin if z<end else'exit'for z in ts);loc.append(tuple(x[:2])+ys if x[0]in('INC','DEC')else('JUMP',*ys)if x[0]=='JUMP'else x)
  require(loc==expected_graph,('local CFG',root,loc));blocks.append((root,begin,end))
  for i in ids:owner[i]=(root,begin,end)
 groups=[];index={};n=0
 while n<len(rows):
  if n in owner:
   root,begin,end=owner[n];require(begin==n,'block boundary');groups.append((n,end,root));n=end
  else:groups.append((n,n+1,None));n+=1
 for j,(a,b,root)in enumerate(groups):
  for i in range(a,b):index[i]=j
 Q=[]
 for j,(a,b,root)in enumerate(groups):
  if root is not None:Q.append(('TRANSFER_PLUS_ONE',6,5,index[b]));continue
  x=g[a];ts=x[2:]if x[0]in('INC','DEC')else x[1:]if x[0]=='JUMP'else()
  for z in ts:
   if z in owner:require(z==owner[z][1],('outside entry interior',a,z))
  ys=tuple(index[z]for z in ts);Q.append(tuple(x[:2])+ys if x[0]in('INC','DEC')else('JUMP',*ys)if x[0]=='JUMP'else x)
 require(start not in owner or start==owner[start][1],'initial interior entry');return Q,index[start]
og=[('DEC',6,1,3),('INC',5,2),('JUMP',0),('INC',5,'exit')];ng=[('INC',5,1),('DEC',6,2,'exit'),('JUMP',0)]
a,ai=quotient(old,og);b,bi=quotient(new,ng);require(a==b and ai==bi,'collapsed graph differs');require(len(a)==5113 and len(old)==5125 and len(new)==5121,'census')
# The local theorem is proved by induction on register6 n: F(0,y)=G(0,y)=y+1;
# F(n+1,y)=F(n,y+1) and G(n+1,y)=G(n,y+1). All recursions decrease n.
# Distinct registers6 and5 ensure both final files are [r6:=0,r5:=n+y+1]
# with every other register unchanged. Both local paths terminate normally,
# so replacing each local terminating block preserves global halting.
out={'status':'INDEPENDENT_COMPLETE_COLLAPSED_CFG_AND_LOCAL_INDUCTION_PASS','input_sites_sha256':sha(P),'output_sites_sha256':sha(D/'sites.json'),'checker_sha256':sha(Path(__file__)),'old_leaves':len(old),'new_leaves':len(new),'collapsed_nodes':len(a),'substitutions':roots,'local_old_graph':og,'local_new_graph':ng,'no_external_interior_entries':True,'local_theorem':'For every natural source n and destination y, both terminate normally with source0, destination n+y+1, and all other registers unchanged. Induct on n using identical base and recursive equations.','global_theorem':'The identical collapsed finite control graph, common entry, and terminating local block theorem give two-way halting equivalence for every natural initial register file.','formalization_status':'Ordinary mathematical proof; no new kernel certificate.'};(OUT/'source_equivalence_independent.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items()if k not in('local_old_graph','local_new_graph')})
