#!/usr/bin/env python3
"""Replay the13 current incoming dense tables through their reported startup.

Every tape cell is represented by membership in a finite set of one-cells;
all other cells are zero. This is a fresh finite-run check only. It makes no
inference about unbounded execution or arithmetic consistency.
"""
from pathlib import Path
import argparse, hashlib, json
from check_novelty import parse_file, require

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();here=Path(__file__).resolve().parent
    recorded=json.loads((here/'incoming13_startup_replay.json').read_text())
    results=[]
    for r in recorded['results']:
        path=here/'incoming_tables'/(r['name']+'.tm')
        require(hashlib.sha256(path.read_bytes()).hexdigest()==r['sha256'],'table identity mismatch')
        rows,states,halt=parse_file(path)
        require(states==set(range(194)) and halt==194,'incorrect machine convention')
        q,h,ones=0,0,set()
        for step in range(r['steps']):
            require(q!=halt,'unexpected early halt')
            w,d,q=rows[q,int(h in ones)]
            if w:ones.add(h)
            else:ones.discard(h)
            h+=1 if d=='R' else -1
        require(q==r['dense_state'] and h==r['head'] and sorted(ones)==r['one_cells'],'complete startup configuration differs')
        results.append({'name':r['name'],'steps':r['steps'],'state':q,'head':h,'complete_tape_equal':True})
    out={'passed':True,'machines':len(results),'results':results,'scope':'Exact finite startup only; no nonhalting or consistency inference.'}
    args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()
