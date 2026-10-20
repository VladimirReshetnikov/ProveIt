#!/usr/bin/env python3
"""Preserve the five original rho8 splice positions while emitting G/H."""
from pathlib import Path
from functools import lru_cache
import argparse,itertools,json,sys,time
sys.path.insert(0,str(Path(__file__).resolve().parent))
import a10_source_search as a
import antecedent_search as aa
import two_row_basis_search as bb
z,s=a.z,a.s
intervals=[(lo,hi)for lo,hi,_ in a.chunks(a.old,135,486)]

def skeleton(n,st=0):
 en=st+len(z.flat(n))
 if(en<=135 or st>=486):return n
 if(st,en)in intervals:return intervals.index((st,en))
 assert not s.leaf(n)
 return skeleton(n[0],st),skeleton(n[1],st+len(z.flat(n[0])))
TEMPLATE=skeleton(a.old)

def instantiate(template,holes):
 if isinstance(template,int):return holes[template]
 if template in aa.oldnodes:return template
 return instantiate(template[0],holes),instantiate(template[1],holes)


def allparses(atoms,width):
 words=[z.flat(n)for n in atoms];pref=[()]
 for w in words:pref.append(pref[-1]+w)
 @lru_cache(None)
 def profile(n):
  if s.leaf(n):return 0,0,0
  la,za,ha=profile(n[0]);lb,zb,hb=profile(n[1]);return 1+la,max(1+la,za,zb),1+max(ha,hb)
 @lru_cache(None)
 def fresh(n):
  if n in aa.oldnodes:return frozenset()
  return frozenset({n}) if s.leaf(n)else fresh(n[0])|fresh(n[1])|{n}
 @lru_cache(None)
 def go(i,j):
  word=pref[j][len(pref[i]):];cs=set(aa.known_word.get(word,()))
  if j==i+1:cs.add(atoms[i])
  for k in range(i+1,j):
   for l in go(i,k):
    for r in go(k,j):
     n=(l,r);p=profile(n)
     if p[1]<=7 and p[2]<=50:cs.add(n)
  return tuple(sorted(cs,key=lambda n:(len(fresh(n)),profile(n)[1],profile(n)[2],str(n)))[:width])
 go(0,len(atoms));return go


def main():
 ap=argparse.ArgumentParser();ap.add_argument('--width',type=int,default=1);ap.add_argument('--all',action='store_true');args=ap.parse_args()
 out=Path(__file__).parent/'basis_chunk_variants';out.mkdir(exist_ok=True)
 permutations=list(itertools.permutations((z.MACRO[166],z.MACRO[121],z.MACRO[168])))
 objective=a.hw.make(a.table,a.old)[0];best=999;results=[];start=time.monotonic()
 recipes=[((1,3),('G','H')),((0,0),('G','H')),((1,3),('H','G'))]
 if args.all:recipes=list(itertools.product(itertools.product(range(6),repeat=2),itertools.permutations(bb.F)))
 for maps,order in recipes:
  atommap={name:aa.emit(formula,permutations[pi])for(name,formula),pi in zip(bb.F.items(),maps)}
  atoms=sum((atommap[name]for name in order),[]);parse=allparses(atoms,args.width);localbest=999;tested=0
  for cuts in itertools.combinations(range(1,len(atoms)),4):
   bounds=(0,)+cuts+(len(atoms),)
   for chunks in itertools.product(*(parse(i,j)for i,j in zip(bounds,bounds[1:]))):
    new=instantiate(TEMPLATE,chunks);score=objective(new);cost=score['cost_lower_bound'];tested+=1
    if cost<localbest:localbest=cost
    if cost<best:
     best=cost;row=dict(parameter_maps=maps,order=order,bounds=bounds,hardware_lower_bound=score,metrics=s.metrics(new));print('BEST',json.dumps(row),flush=True)
     d=out/('best_'+str(best));d.mkdir(exist_ok=True);rows=s.sites(new)
     assert z.flat(new)==z.flat(a.old)[:135]+sum((z.flat(n)for n in atoms),())+z.flat(a.old)[486:]
     assert s.graph_arithmetic(rows)[0]==s.graph_intervals(rows)
     (d/'sites.json').write_bytes(s.compact(rows));(d/'receipt.json').write_text(json.dumps(row,indent=2)+'\n')
  row=dict(parameter_maps=maps,order=order,tested=tested,best=localbest);results.append(row);print('RECIPE',json.dumps(row),'seconds',round(time.monotonic()-start,2),flush=True)
  (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
 print('DONE',len(results),'best',best,'seconds',time.monotonic()-start,flush=True)

if __name__=='__main__':main()
