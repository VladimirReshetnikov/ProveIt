#!/usr/bin/env python3
"""Repeat the five explicitly scoped searches; do not infer a state lower bound."""
import argparse, hashlib, json, subprocess, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    a.output.mkdir(parents=True,exist_ok=False)
    provenance=json.loads((ROOT/'PROVENANCE.json').read_text())
    for path,rec in provenance['files'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==rec['sha256'],path
    tests=[('r41.native.tm','r41-depth4',4,45,200,71380),
           ('r41.native.tm','r41-depth8',8,97,1000,99760),
           ('shallow.native.tm','shallow-depth8',8,97,1000,108360),
           ('gc-zc.canonical.tm','gczc-depth8',8,97,1000,97180)]
    receipts=[]
    for table,name,depth,steps,nodes,count in tests:
        out=a.output/(name+'.json')
        cmd=[sys.executable,'-B',str(ROOT/'code/context_search.py'),str(ROOT/'inputs'/table),
             '--output',str(out),'--depth',str(depth),'--steps',str(steps),'--nodes',str(nodes)]
        subprocess.run(cmd,check=True)
        got=json.loads(out.read_text());assert got['status']=='BOUNDED_SEARCH_NO_SURVIVOR'
        assert got['specifications']==count and got['survivors']==[]
        receipts.append({'name':name,'specifications':count,'status':got['status']})
    out=a.output/'r41-blank-window'
    subprocess.run([sys.executable,'-B',str(ROOT/'code/blankfolds/search.py'),
                    '--seed',str(ROOT/'inputs/r41.native.tm'),'--output',str(out),'--seconds','110'],check=True)
    got=json.loads((out/'result.json').read_text())
    assert got['status']=='COMPLETE_BOUNDED_SEARCH', 'Search did not complete within inherited time ceiling'
    assert got['stats']['completed_pairs']==46010 and got['stats']['attempted']==632584
    assert got['stats']['filter_rejected']==632584 and got['hits']==[]
    receipts.append({'name':'r41-blank-window','specifications':632584,'status':got['status']})
    (a.output/'reproduction.json').write_text(json.dumps({'status':'ALL_FIVE_SEARCH_RECEIPTS_REPRODUCED','results':receipts},indent=2)+'\n')
if __name__=='__main__':main()
