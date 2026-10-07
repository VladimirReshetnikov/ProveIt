"""Strict integration gate for an existing ProveIt fast/ checkout.

This script was supplied but NOT EXECUTED against upstream in this research run.
It never installs dependencies or changes the upstream tree.
"""
import argparse
import json
import sys
from pathlib import Path


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--fast-dir',type=Path,required=True,help='directory containing fastunknot/')
    parser.add_argument('--cases',type=Path,default=Path(__file__).resolve().parents[1]/'results/validation.json')
    parser.add_argument('--limit',type=int,default=200)
    parser.add_argument('--output',type=Path,default=Path('results/upstream_crosscheck.json'))
    args=parser.parse_args()
    if args.limit<1: parser.error('--limit must be positive')
    sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
    sys.path.insert(0,str(args.fast_dir.resolve()))
    from fastunknot.diagram import Diagram
    from fastunknot.scan import khovanov_rank
    from twistkh import homology,runs_from_word
    rows=json.loads(args.cases.read_text())['rows'];checked=[]
    for case in rows:
        if case['components']!=1: continue
        b,w=case['strands'],case['word'];d=Diagram.from_braid(b,w)
        ref=khovanov_rank(d.pd,check_d_squared=True,seconds=30)
        ours=homology(b,runs_from_word(b,w),check_d2=True)
        if any(v%2 for v in ref['by_degree'].values()): raise AssertionError('upstream unreduced parity failure')
        # Upstream SMOOTHINGS[0] is (a,b)(c,d); positive braid crossings give E,
        # whereas ours starts positive crossings with I. The cubes are dual.
        # Thus our normalized h = n_positive - upstream cube degree.
        npos=sum(x>0 for x in w)
        normalized={npos-int(k):v//2 for k,v in ref['by_degree'].items() if v}
        if normalized!=ours['by_degree'] or ref['reduced_rank']!=ours['reduced_rank']:
            raise AssertionError({'case':case,'upstream':ref,'macro':ours})
        checked.append({'strands':b,'word':w,'rank':ours['reduced_rank']})
        if len(checked)>=args.limit: break
    if not checked: raise RuntimeError('no knot cases were checked')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps({'checked':len(checked),'mismatches':0,'rows':checked},indent=2)+'\n')
    print(f'{len(checked)} upstream comparisons passed')

if __name__=='__main__': main()
