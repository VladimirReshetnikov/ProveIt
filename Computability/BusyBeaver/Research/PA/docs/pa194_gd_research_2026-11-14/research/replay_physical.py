#!/usr/bin/env python3
"""Replay the radius-four, 100-step joint two-row quotient search.

Uses the bundled source-context windows unless --regenerate-contexts is given.
This finite model is a search screen, not a lower bound on Turing-machine size.
"""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
ALIASES={'GD':'sum','GDH':'H','GDHS':'HS'}

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('family',choices=list(ALIASES))
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--compiler',default='g++')
 p.add_argument('--regenerate-contexts',action='store_true')
 p.add_argument('--compile-only',action='store_true')
 a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 compiler=shutil.which(a.compiler)
 if not compiler:raise SystemExit('C++17 compiler not found: '+a.compiler)
 source=HERE/'physical/inherited/src/joint_return_merge.cpp'
 executable=(a.output/'joint_return_merge').resolve()
 subprocess.run([compiler,'-O3','-std=c++17',str(source),'-o',str(executable)],check=True)
 if a.compile_only:print(json.dumps({'compiled':str(executable)}));return
 machine=ROOT/'machines'/a.family;table=machine/'machine.native.tm'
 contexts=HERE/'physical'/(ALIASES[a.family]+'_contexts4.txt')
 if a.regenerate_contexts:
  contexts=(a.output/'contexts4.txt').resolve()
  with (a.output/'contexts_receipt.json').open('w') as log:
   subprocess.run([sys.executable,str(HERE/'physical/inherited/src/collect_source_contexts.py'),
                   str(table),str(machine/'sites.json'),str(machine/'instructions.json'),str(contexts),'4'],stdout=log,check=True)
 command=[str(executable),str(table),'4','100',str(contexts)]
 with (a.output/'hits.jsonl').open('w') as hits,(a.output/'search.log').open('w') as log:
  subprocess.run(command,stdout=hits,stderr=log,check=True)
 done=[z for z in (a.output/'search.log').read_text().splitlines()if z.startswith('DONE ')]
 receipt={'family':a.family,'radius':4,'step_bound':100,'completion':done[-1]if done else None,
          'table_sha256':hashlib.sha256(table.read_bytes()).hexdigest(),
          'contexts_sha256':hashlib.sha256(contexts.read_bytes()).hexdigest(),
          'source_contexts_regenerated':a.regenerate_contexts,
          'scope':'Local one-control quotient with two synthesized actions; source contexts exclude startup and do not narrow the arithmetic engine.'}
 (a.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt))
if __name__=='__main__':main()
