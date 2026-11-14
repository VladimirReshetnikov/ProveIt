from pathlib import Path
import sys,json
P=Path(__file__).resolve().parents[2] / 'reference' / 'pa194';W=Path(__file__).resolve().parent
sys.path.insert(0,str(P/'construction'));import compiler as c
base=c.raw_nodes(); ax=c.read_grammar(P/'construction/source/pa194.grammar.json')
def source(nodes):
 sites=[];active=set()
 def walk(t,p=(),inside=False):
  if isinstance(t,str):
   if t=='x67':return walk(ax,p,True)
   active.add(t);return walk(nodes[t],p,inside)
  if t[0]=='leaf':sites.append((p,t[1],t[2],inside));return
  walk(t[0],p+(0,),inside);walk(t[1],p+(1,),inside)
 walk('node172');lookup={};leaves={p:i for i,(p,op,arg,a) in enumerate(sites)}
 for i,(p,op,arg,a) in enumerate(sites):
  for k in range(len(p)+1):lookup.setdefault(p[:k],i)
 def locate(p):
  if p in lookup:return lookup[p]
  while p and not p[-1]:
   p=p[:-1]
   if p in leaves:return leaves[p]
  raise ValueError('missing path')
 def after(p):
  i=len(p)-1
  while i>=0 and p[i]:i-=1
  if i<0:raise ValueError('exit')
  return locate(p[:i]+(1,))
 def cut(p,b,k):
  for i in range(len(p)-1,-1,-1):
   if p[i]==b:
    k-=1
    if not k:return p[:i]
  raise ValueError('cut')
 instructions=[]
 for p,op,arg,a in sites:
  if op=='inc':x=('inc',arg,after(p))
  elif op=='dec':x=('dec',arg,after(cut(p,0,1)),after(p))
  elif op=='breakTo':x=('jump',after(cut(p,0,arg)))
  elif op=='continueTo':x=('jump',locate(cut(p,1,arg)))
  elif op=='halt':x=('halt',)
  else:raise ValueError(op)
  instructions.append(x)
 return sites,instructions,active
orig,ins,active=source(base)
def zrun(p):return max(map(len,''.join(map(str,p)).split('1')))
def stats(sites):
 outside=[(i,p,op) for i,(p,op,arg,a) in enumerate(sites) if not a]
 return {'max_zero_all':max(zrun(p) for p,op,arg,a in sites),'outside_maxzero':max(zrun(p) for i,p,op in outside),'site25':''.join(map(str,sites[25][0])),'outside_over5':[(i,''.join(map(str,p)),op) for i,p,op in outside if zrun(p)>5]}
print('ORIGINAL',json.dumps(stats(orig)))
res=[]
for name in sorted(active):
 t=base[name]
 for side in (0,1):
  child=t[side]
  if isinstance(child,str):child=base.get(child)
  if not c.isnode(child):continue
  new=(child[0],(child[1],t[1])) if side==0 else ((t[0],child[0]),child[1])
  nodes=dict(base);nodes[name]=new
  try:sites,newins,_=source(nodes)
  except ValueError:continue
  same=newins==ins
  r={'name':name,'side':side,'replacement':new,'source_equal':same,'instruction_differences':sum(x!=y for x,y in zip(ins,newins)),**stats(sites)}
  if same:print('VALID',json.dumps(r))
  res.append(r)
(W/'outer_rotations.json').write_text(json.dumps({'original':stats(orig),'cases':res},indent=2)+'\n')
