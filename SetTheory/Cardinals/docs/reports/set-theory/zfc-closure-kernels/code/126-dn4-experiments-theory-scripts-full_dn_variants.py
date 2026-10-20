from pathlib import Path
import json,itertools
from functools import cache
import flatten_macros as f
b=f.b;root=f.m.root
nodes={}
for n,name in f.macros.items():nodes.setdefault(name,n)
oldx=(nodes['and'],nodes['ex'])
oldb=(nodes['and'],(nodes['and'],nodes['ac_s1s2']))
print('bundle match',f.m.paths.get(oldb,[]),'leaves',len(b.sites(oldb)))
@cache
def shapes(n):
 if n==1:return (0,)
 def at(t,off):return t+off if type(t)==int else tuple(at(x,off) for x in t)
 return tuple((x,at(y,k)) for k in range(1,n) for x in shapes(k) for y in shapes(n-k))
def build(t,items):return items[t] if type(t)==int else tuple(build(x,items) for x in t)
itemsx=[nodes[n] for n in ['neg','im','all','neg']]
itemsb=[nodes[n] for n in ['neg','im','im','neg','ac_s1s2']]
out=f.m.e.OUTPUT_ROOT/'full_dn';out.mkdir(parents=True,exist_ok=True)
results=[]
for i,sx in enumerate(shapes(4)):
 nx=build(sx,itemsx)
 for j,sb in enumerate(shapes(5)):
  nb=build(sb,itemsb)
  def repl(n):
   if n==oldx:return nx
   if n==oldb:return nb
   return n if b.is_leaf(n) else tuple(map(repl,n))
  r=repl(root);stats=b.metrics(r)
  if stats['maximum_zero_run']>6:continue
  try:b.graph(b.sites(r))
  except Exception:continue
  results.append((stats['dag_nodes'],i,j,stats,sx,sb,r))
results.sort(key=lambda x:(x[0],x[3]['maximum_depth'],x[1],x[2]))
for k,row in enumerate(results[:10]):
 _,i,j,stats,sx,sb,r=row
 print(k,i,j,stats,'shapes',sx,sb)
 (out/f'sites_full_dn{k}.json').write_bytes(b.json_bytes(b.sites(r),compact=True))
 (out/f'replacement_x{k}.json').write_bytes(b.json_bytes(b.sites(build(sx,itemsx)),compact=True))
 (out/f'replacement_b{k}.json').write_bytes(b.json_bytes(b.sites(build(sb,itemsb)),compact=True))
 (out/f'recipe{k}.json').write_bytes(b.json_bytes({'and_ex_paths':f.m.paths.get(oldx,[]),'and_and_acdup_paths':f.m.paths.get(oldb,[]),'shape_x':sx,'shape_b':sb,'metrics':stats}))
