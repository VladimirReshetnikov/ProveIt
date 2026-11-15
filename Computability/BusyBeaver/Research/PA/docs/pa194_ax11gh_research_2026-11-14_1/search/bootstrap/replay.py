#!/usr/bin/env python3
"""Replay three bounded 193-state startup searches; no general lower bound."""
from pathlib import Path
import argparse, json, subprocess

ROOT = Path(__file__).resolve().parent

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--suite',choices=('pairs','marker','joint','all'),default='joint')
    ap.add_argument('--out',type=Path,default=ROOT/'replayed')
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    cases={
      'pairs': ('search_pair_startup',[ROOT/'runtime193.native.tm',ROOT/'neutral_pool.tsv',500000,0,1000,ROOT/'startup_any_frame_templates.tsv']),
      'marker': ('search_marker_rescue',[ROOT/'runtime193.native.tm',ROOT/'neutral_pool.tsv',200000,0,1000,ROOT/'startup_any_frame_templates.tsv']),
      'joint': ('joint_marker_search',[ROOT/'runtime193.native.tm',ROOT/'runtime193_contexts_k6.txt',100]),
    }
    results=[]
    for name in (cases if a.suite=='all' else [a.suite]):
        program,args=cases[name];binary=a.out/program
        subprocess.run(['g++','-O3','-std=c++17',str(ROOT/(program+'.cpp')),'-o',str(binary)],check=True)
        hits=a.out/(name+'_hits.jsonl');log=a.out/(name+'.log')
        with hits.open('w') as out,log.open('w') as err:
            subprocess.run([str(binary),*map(str,args)],stdout=out,stderr=err,check=True)
        if hits.read_text().strip():
            raise SystemExit(f'Found a new hit in {hits}; inspect it, do not accept the old negative result.')
        result=dict(suite=name,hits=0,last_log_line=log.read_text().strip().splitlines()[-1])
        results.append(result);print(json.dumps(result),flush=True)
    (a.out/'receipt.json').write_text(json.dumps(results,indent=2)+'\n')

if __name__=='__main__':main()
