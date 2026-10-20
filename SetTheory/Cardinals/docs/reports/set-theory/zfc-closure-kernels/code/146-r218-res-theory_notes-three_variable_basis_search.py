#!/usr/bin/env python3
"""Screen the sound Tarski--Bernays three-variable implication basis.

K: p -> (q -> p)
P: ((p -> q) -> p) -> p
H: (p -> q) -> ((q -> r) -> (p -> r))

Replace the rho8 emitter by consecutive K/P/H emissions, removing its
fourth-parameter stream reader. This changes the enumerated AX format
and leaves two more theorem codes on the stack. Results are hardware
lower bounds, not accepted machine tables.
"""
from pathlib import Path
import argparse
import itertools
import json
import sys
import time

sys.path.insert(0,str(Path(__file__).resolve().parent))
import a10_source_search as a
import antecedent_search as aa
z,s=a.z,a.s
I=z.I
F={
 'K':I('a',I('b','a')),
 'P':I(I(I('a','b'),'a'),'a'),
 'H':I(I('a','b'),I(I('b','c'),I('a','c'))),
}


def main():
 ap=argparse.ArgumentParser()
 ap.add_argument('--width',type=int,default=3)
 ap.add_argument('--independent',action='store_true')
 ap.add_argument('--out',type=Path,default=Path(__file__).parent/'three_basis_variants')
 args=ap.parse_args();args.out.mkdir(exist_ok=True)
 permutations=list(itertools.permutations((z.MACRO[166],z.MACRO[121],z.MACRO[168])))
 objective=a.hw.make(a.table,a.old)[0]
 best=999;results=[];start=time.monotonic()
 parameter_maps=itertools.product(range(6),repeat=3) if args.independent else ((i,i,i)for i in range(6))
 for maps in parameter_maps:
  atommap={name:aa.emit(formula,permutations[pi])for (name,formula),pi in zip(F.items(),maps)}
  for order in itertools.permutations(F):
   atoms=sum((atommap[name]for name in order),[])
   for ni,n in enumerate(aa.parses(atoms,args.width)):
    for last in (False,True):
     new=a.splice(a.old,135,486,n,last)
     cost=objective(new);metrics=s.metrics(new)
     row=dict(order=order,parameter_maps=maps,parse=ni,insert_last=last,metrics=metrics,hardware_lower_bound=cost)
     results.append(row)
     score=cost['cost_lower_bound']
     if score<best:
      best=score
      print('BEST',json.dumps(row),flush=True)
      d=args.out/('best_'+str(best));d.mkdir(exist_ok=True)
      rows=s.sites(new)
      assert s.graph_arithmetic(rows)[0]==s.graph_intervals(rows)
      (d/'sites.json').write_bytes(s.compact(rows))
      (d/'receipt.json').write_text(json.dumps(row,indent=2)+'\n')
  print('MAP',maps,'best',best,'n',len(results),'seconds',round(time.monotonic()-start,2),flush=True)
 (args.out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
 print('DONE',len(results),'best',best,'seconds',time.monotonic()-start,flush=True)

if __name__=='__main__':main()
