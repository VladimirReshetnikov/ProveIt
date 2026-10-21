#!/usr/bin/env python3
"""Finite literal register-program checks of the two S2 guarded equations."""
from pathlib import Path
import argparse
import json
import build_source as src


def P(a,b):return (a+b)*(a+b+1)//2+b


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',type=Path,default=Path(__file__).with_name('stride2-0.sites.json'))
    ap.add_argument('--output',type=Path,default=Path(__file__).with_name('source_command_checks.json'))
    ap.add_argument('--direct',action='store_true',help='Check clear/load/NIP/NIP and its h-or-x guard')
    a=ap.parse_args()
    root=src.tree(json.loads(a.source.read_bytes()));body=src.sub(root,src.PATH)
    rows=src.sites((body,('CH',None)));g=src.graph(rows)
    assert g==src.graph_binary(rows)
    terminal=len(rows)-1;cases=halting=maxsteps=0
    for top in range(3):
      for cache in range(3):
       for x in range(3):
        for y in range(3):
         for tail in range(1):
          regs=[7,top,P(x,P(y,tail)),0,3,cache,0,0,11]
          expected=[7,cache,tail,0,3,y,0,0,11]
          pc=0
          for steps in range(100000):
            op,r,to=g[pc]
            if op=='CH':break
            if op=='CI':regs[r]+=1;pc=to[0]
            elif op=='CD':
                b=int(regs[r]>0);regs[r]-=b;pc=to[b]
            else:pc=to[0]
          else:raise AssertionError(('explicit finite instruction cap exceeded',top,cache,x,y,tail,pc,regs))
          bad=cache==1 or x==1 or (top==1 and not a.direct)
          assert (pc!=terminal)==bad,(top,cache,x,y,tail,pc,regs)
          if not bad:assert regs==expected,(top,cache,x,y,tail,regs,expected)
          cases+=1;halting+=bad;maxsteps=max(maxsteps,steps)
    report={'status':'LITERAL_STRIDE_TWO_COMMAND_FINITE_PASS','cases':cases,
            'exact_guard_halts':halting,'maximum_primitive_steps':maxsteps,
            'return_equation':'(t,[x,y;S],d,h) -> (h,S,d,y)',
            'exact_halt_guard':'h=1 OR x=1' if a.direct else 'h=1 OR t=1 OR x=1',
            'scope':'Finite actual source execution, corroborating the written command equation; not all-natural or physical machine verification.'}
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))


if __name__=='__main__':main()
