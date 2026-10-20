#!/usr/bin/env python3
"""Keep the old fourth reader as the single q occurrence of G or G'."""
from pathlib import Path
import itertools,json,sys,time
sys.path.insert(0,str(Path(__file__).resolve().parent))
import a10_source_search as a
import antecedent_search as aa
z,s=a.z,a.s;I=z.I
F={'G':I(I(I('a','b'),'a'),I('c','a')),'Gprime':I('c',I(I(I('a','b'),'a'),'a'))}
H=I(I('a','b'),I(I('b','c'),I('a','c')))
def main():
 out=Path(__file__).parent/'retained_reader_split_variants';out.mkdir(exist_ok=True)
 perms=list(itertools.permutations((z.MACRO[166],z.MACRO[121],z.MACRO[168])))
 objective=a.hw.make(a.table,a.old)[0];best=999;results=[];start=time.monotonic()
 for name,G in F.items():
  for pi,p in enumerate(perms):
   gp=(p[0],a.reader,p[2]);atomsG=sum(([part for _,_,part in a.chunks(a.old,161,194)] if atom==a.reader else [atom] for atom in aa.emit(G,gp)),[])
   for hi,hp in enumerate(perms):
    atomsH=aa.emit(H,hp)
    for reverse in (False,True):
     atoms=atomsH+atomsG if reverse else atomsG+atomsH
     for n in aa.parses(atoms,1):
      for last in (False,True):
       new=a.splice(a.old,135,486,n,last);score=objective(new);cost=score['cost_lower_bound']
       row=dict(basis=name,permutation_G=pi,permutation_H=hi,reverse=reverse,insert_last=last,metrics=s.metrics(new),hardware_lower_bound=score);results.append(row)
       if cost<best:
        best=cost;print('BEST',json.dumps(row),flush=True);d=out/('best_'+str(best));d.mkdir(exist_ok=True);rows=s.sites(new)
        assert s.graph_arithmetic(rows)[0]==s.graph_intervals(rows)
        (d/'sites.json').write_bytes(s.compact(rows));(d/'receipt.json').write_text(json.dumps(row,indent=2)+'\n')
   print('PARAM',name,pi,'best',best,'cases',len(results),'seconds',round(time.monotonic()-start,2),flush=True)
 (out/'results.json').write_text(json.dumps(results,indent=2)+'\n');print('DONE',len(results),best,time.monotonic()-start,flush=True)
if __name__=='__main__':main()
