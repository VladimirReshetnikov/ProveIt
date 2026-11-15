#!/usr/bin/env python3
"""Compile and rerun one of the eight recorded bounded grammar searches.

Wall-time stopping makes mutation totals machine dependent. This starts from
the exact bundled templates, attributes and random seed, preserving the logs.
"""
from pathlib import Path
import argparse,json,re,shutil,subprocess
ROOT=Path(__file__).resolve().parent
RUNS={z['name']:z for z in json.loads((ROOT/'grammar/summary.json').read_text())}

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('run',choices=list(RUNS))
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--seconds',type=float,help='Default 600 seconds, or 300 for head_order; zero checks input loading only.')
 p.add_argument('--seed',type=int,help='Defaults to the recorded seed.')
 p.add_argument('--compiler',default='g++')
 p.add_argument('--compile-only',action='store_true')
 a=p.parse_args();compiler=shutil.which(a.compiler)
 if not compiler:raise SystemExit('C++17 compiler not found: '+a.compiler)
 a.output.mkdir(parents=True,exist_ok=True)
 head=a.run=='head_order';src=ROOT/'grammar/head_order/search_order.cpp' if head else ROOT/'grammar/search.cpp'
 templates=ROOT/'grammar/head_order/order_templates.txt' if head else ROOT/'grammar'/a.run/'templates.txt'
 attrs=ROOT/'grammar/head_order/inputs/leaf_attrs.txt' if head else ROOT/'grammar/leaf_attrs.txt'
 executable=(a.output/('head_order_search'if head else'grammar_search')).resolve()
 subprocess.run([compiler,'-O3','-std=c++17',str(src),'-o',str(executable)],check=True)
 if a.compile_only:print(json.dumps({'compiled':str(executable)}));return
 seconds=a.seconds if a.seconds is not None else (300 if head else 600)
 if seconds<0:raise SystemExit('Duration must be nonnegative')
 seed=a.seed if a.seed is not None else RUNS[a.run].get('seed',20261115)
 prefix=(a.output/'search').resolve()
 command=[str(executable),str(templates),str(attrs),str(prefix),str(seconds),str(seed)]
 with (a.output/'search.log').open('w') as log:
  subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True)
 lines=(a.output/'search.log').read_text().splitlines();done=[z for z in lines if z.startswith('DONE ')]
 receipt={'run':a.run,'seconds_requested':seconds,'seed':seed,'input_templates':str(templates.relative_to(ROOT)),
          'source':str(src.relative_to(ROOT)),'completion':done[-1] if done else None,
          'scope':'Bounded heuristic search; a hit would still require exact semantic and physical verification.'}
 (a.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt))
if __name__=='__main__':main()
