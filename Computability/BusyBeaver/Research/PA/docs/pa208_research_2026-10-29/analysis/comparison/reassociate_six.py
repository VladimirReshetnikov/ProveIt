from pathlib import Path
from functools import lru_cache
import json,sys,subprocess
sys.dont_write_bytecode=True
import search_directional as D
L=D.L
@lru_cache(None)
def shapes(lo,hi):
 if hi-lo==1:return(lo,)
 return tuple((a,b)for mid in range(lo+1,hi)for a in shapes(lo,mid)for b in shapes(mid,hi))
def main():
 b=D.I.base;t=D.I.read(b/'machine/variant_plain/u208.native.tm');ss=json.loads((b/'machine/variant_plain/u208.sites.json').read_text());root=L.tree(ss);_,occ,_=D.I.inventory(t,ss)
 path,node=occ[174][0];atoms=[next(n for p,n in occ[q]if len(L.sites(n))==sz)for q,sz in[(98,26),(158,134),(147,52),(146,108),(220,136),(214,264)]]
 targets=[98,158,147,146,220,214];slots=[174,129,204,215,217];all=[];out=D.S.work/'six_factor';out.mkdir(exist_ok=True);D.out=out
 for index,shape in enumerate(shapes(0,6)):
  assigned={};nextslot=iter(slots);nt=dict(t);parents={}
  def build(s):
   if isinstance(s,int):return targets[s],atoms[s]
   q=next(nextslot);a,na=build(s[0]);b,nb=build(s[1]);nt[q,0]=(0,1,a);nt[q,1]=(1,1,b);parents[a]=(q,0);parents[b]=(q,1);return q,(na,nb)
  nq,nn=build(shape)
  if parents[158][1]!=0 or parents[220][1]!=0:continue
  nt[220,0]=(0,-1,parents[158][0]);nr=L.replace(root,path,nn);mt,folds=D.S.merge(nt)
  if L.graph_intervals(L.sites(nr))!=L.graph_intervals(ss):raise ValueError('CFG altered')
  rec=D.test(mt,nr,[('six_shape',shape,'helper',parents[158][0])],folds,index);all.append(rec)
 (out/'results.json').write_text(json.dumps(all,indent=2)+'\n')
if __name__=='__main__':main()
