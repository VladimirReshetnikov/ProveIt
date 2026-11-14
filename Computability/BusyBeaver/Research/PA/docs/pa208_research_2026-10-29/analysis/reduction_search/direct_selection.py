from pathlib import Path
import sys,json,itertools
sys.dont_write_bytecode=True;sys.path.insert(0,'analysis/comparison');import source_inventory as I
L=I.L;src=I.base/'machine/variant_plain/u208.sites.json';rows=json.loads(src.read_text());root=L.tree(rows)

def alltrees(xs):
 if len(xs)==1:return xs
 return [(a,b)for k in range(1,len(xs))for a in alltrees(xs[:k])for b in alltrees(xs[k:])]

def run(tree,store,cap=10000):
 end=len(L.sites(tree));rs=L.sites((tree,('CI',0)));g=L.graph_arithmetic(rs)[0];i=0;store=store[:]
 for steps in range(cap):
  if i==end:return store,False,steps
  eff,targets=g[i];op,arg=rs[i][1:]
  if op=='CH':return store,True,steps+1
  if op=='CI':store[arg]+=1;i=targets[0]
  elif op=='CD':
   b=int(store[arg]>0);store[arg]-=b;i=targets[b]
  else:i=targets[0]
 raise RuntimeError('cap')

clear=L.subtree(root,'01');copy=L.subtree(root,'100');pop=L.subtree(root,'1111')
assert len(L.sites(clear))==2 and len(L.sites(copy))==4 and len(L.sites(pop))==14
nothalt=lambda r:((('CD',r),('CB',1)),('CH',None))
transfer=(('CD',5),(('CI',1),('CC',2)))
variants=[]
for j,b in enumerate(alltrees([('CI',1),nothalt(5),('CI',1),transfer])):
 body=(('CD',5),b);new=(root[0],(body,pop));variants.append((f'direct25_{j}',new,body))
for j,b in enumerate(alltrees([copy,(('CD',6),(nothalt(6),(('CD',6),('CC',1))))])):
 new=(root[0],(b,pop));variants.append((f'copy26_{j}',new,b))

out=Path('analysis/reduction_search/direct_selection');out.mkdir(exist_ok=True)
results=[]
for tag,new,body in variants:
 nr=L.sites(new);g=L.graph_arithmetic(rows)[0];ng=L.graph_arithmetic(nr)[0];assert g==L.graph_intervals(rows) and ng==L.graph_intervals(nr);lo=3876;hi=3895;newhi=lo+len(L.sites(body));delta=newhi-hi
 assert nr[:lo]==rows[:lo]
 assert [(o,a)for _,o,a in nr[newhi:]]==[(o,a)for _,o,a in rows[hi:]]
 for i,(eff,zs)in enumerate(g):
  if lo<=i<hi:continue
  idx=i if i<lo else i+delta
  expected=[z if z<=lo else newhi if z==hi else z+delta if z>=hi else None for z in zs]
  assert None not in expected,(i,zs)
  assert ng[idx]==[eff,expected],(i,ng[idx],eff,expected)
 # The pre-pop transformer is meaningful independently of Cantor code sizes.
 macro=(clear,body);cases=0
 for t,h in itertools.product(range(16),repeat=2):
  s=[9,t,37,0,11,h,0,0,13]
  result,halt,steps=run(macro,s)
  assert halt==(h==1),(tag,t,h,result,halt)
  if not halt:
   expected=s[:];expected[1]=h;expected[5]=0
   assert result==expected,(tag,t,h,result,expected)
  cases+=1
 (out/f'{tag}.sites.json').write_text(json.dumps(nr,separators=(',',':'))+'\n')
 (out/f'{tag}.sites.tsv').write_text(''.join(f'{p}\t{o}\t{a if a is not None else -1}\n'for p,o,a in nr))
 (out/f'{tag}.macro.json').write_text(json.dumps(L.sites(macro),indent=2)+'\n')
 results.append({'name':tag,'metrics':L.metrics(new),'new_selection_primitives':2+len(L.sites(body))+14,'retained_CFG_check':True,'startup136_unchanged':nr[136]==rows[136],'finite_prepop_cases':cases})
print(json.dumps(results,indent=2));(out/'report.json').write_text(json.dumps(results,indent=2)+'\n')
