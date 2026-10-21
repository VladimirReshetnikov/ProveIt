#!/usr/bin/env python3
"""Bounded source-only price of standard three-parameter classical bases."""
from pathlib import Path
import os
import sys,json,itertools,collections,time
HERE=Path(__file__).resolve().parent
Z=Path(os.environ.get('PROVEIT_ZFC_ROOT', str(HERE.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC'))).resolve()
sys.path.insert(0,str(Z/'k218-quantifier-stability/pricing'))
import source_language as s,build221 as b,measure_pinned as m
class p:
 @staticmethod
 def combine(ts, shape):
  if len(ts)==1:return ts[0]
  k=1 if shape=='right' else len(ts)-1 if shape=='left' else len(ts)//2
  return p.combine(ts[:k],shape),p.combine(ts[k:],shape)
 @staticmethod
 def rename(t,mapping):
  if not isinstance(t,tuple):return mapping.get(t,t)
  return t[0],p.rename(t[1],mapping),p.rename(t[2],mapping)
 @staticmethod
 def postfix(t):
  if not isinstance(t,tuple):return[t]
  return p.postfix(t[1])+p.postfix(t[2])+[t[0]]
I=lambda a,b:('I',a,b)
a,bb,c='a','b','c'
K=I(a,I(bb,a));B=I(I(a,bb),I(I(bb,c),I(a,c)))
Peirce=I(I(I(a,bb),a),a)
S=I(I(a,I(bb,c)),I(I(a,bb),I(a,c)))
def main():
 src=Z/'candidate-k218'
 tree=s.tree(json.loads((src/'sites218.json').read_text()))
 table=b.read_table((src/'k218.native.tm').read_bytes());groups,_=b.decoder_map(table,tree)
 q=lambda k:b.sole(groups,k)
 macros={'a':q(98),'b':q(12),'c':q(166),'I':q(90)}
 assert all(s.boundary(v)==(0,0,False)for v in macros.values())
 for name,forms in [('KBP',[K,B,Peirce]),('KSP',[K,S,Peirce])]:
  out=HERE/('price-'+name);out.mkdir(exist_ok=True)
  start=time.monotonic();best=999;count=0;keep=[];hist=collections.Counter()
  for pp in itertools.product(list(itertools.permutations('abc')),repeat=3):
   fs=[p.rename(f,dict(zip('abc',x)))for f,x in zip(forms,pp)]
   words=[p.postfix(f)for f in fs]
   for shape in ['right','left','balanced']:
    blocks=[p.combine([macros[x]for x in w],shape)for w in words]
    for order in itertools.permutations(range(3)):
     replacement=p.combine([blocks[i]for i in order],shape)
     variant=m.splice(s,tree,135,486,replacement)
     met=s.metrics(variant);count+=1;score=(met['dag_nodes'],met['maximum_zero_run'],met['maximum_depth']);hist[score]+=1
     if met['dag_nodes']<best:
      best=met['dag_nodes'];print(name,'BEST',count,score,pp,shape,order,round(time.monotonic()-start,3),flush=True)
     if met['maximum_zero_run']<=6 and (len(keep)<12 or score<keep[-1][0]):
      info=dict(permutations=pp,shape=shape,order=order,source_metrics=met,words=[words[i]for i in order])
      keep.append((score,info,variant));keep.sort(key=lambda x:x[0]);keep=keep[:12]
  for k,(score,info,t)in enumerate(keep):
   d=out/f'candidate{k:02d}';d.mkdir(exist_ok=True);rows=s.sites(t)
   assert s.graph_arithmetic(rows)[0]==s.graph_intervals(rows)
   (d/'sites.json').write_bytes(s.compact(rows))
   try:
    tt,cm=m.compile_tree(s,b,table,tree,t);info['compiler']=cm;(d/'raw.tm').write_bytes(b.table_bytes(tt))
   except (ValueError,KeyError,AssertionError)as e:info['compiler_error']=repr(e)
   (d/'result.json').write_text(json.dumps(info,indent=2))
  result=dict(basis=name,trials=count,best_dag=best,seconds=time.monotonic()-start,kept=[v[1]for v in keep],scope='Source-only fixed-shape pricing, no runtime or startup validation.')
  (out/'result.json').write_text(json.dumps(result,indent=2));print(name,'DONE',count,best,round(time.monotonic()-start,3),flush=True)
if __name__=='__main__':main()
