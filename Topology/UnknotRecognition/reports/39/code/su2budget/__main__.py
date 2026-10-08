from __future__ import annotations
import argparse
import json
from pathlib import Path
from .slp import Presentation
from .dihedral import solve as compressed
from .univariate import solve as univariate
from .degrees import profile,greedy_cap
from .multivariate import compile_formula


def main():
    parser=argparse.ArgumentParser(description='Exact presentation-level SU(2) research tools')
    parser.add_argument('command',choices=('two-meridians','univariate','profile','wolfram'))
    parser.add_argument('input',type=Path)
    parser.add_argument('--degree-cap',type=int,default=16)
    parser.add_argument('--all-checkpoints',action='store_true')
    args=parser.parse_args()
    p=Presentation.from_dict(json.loads(args.input.read_text()))
    if args.command=='two-meridians': out=compressed(p)
    elif args.command=='univariate': out=univariate(p)
    else:
        pr=profile(p,p.products()) if args.all_checkpoints else greedy_cap(p,args.degree_cap)
        if args.command=='wolfram':
            print(compile_formula(p,pr.checkpoints).wolfram(),end=''); return
        out=dict(rank=p.rank,live_nodes=len(p.live()),live_products=len(p.products()),
                 checkpoints=list(pr.checkpoints),real_variables=pr.dimension,
                 formal_degree=pr.delta,kappa=pr.kappa)
    print(json.dumps(out,indent=2))

if __name__=='__main__': main()
