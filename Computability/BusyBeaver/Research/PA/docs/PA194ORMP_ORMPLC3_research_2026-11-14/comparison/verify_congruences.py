#!/usr/bin/env python3
"""Check ordinary action/target congruence sizes for all548 spanning tables.

This is a restricted static quotient calculation. It is not a lower bound
for context-dependent TM transformations or for blank-start consistency
machines in general.
"""
from pathlib import Path
from collections import Counter
import argparse,csv,gzip,json
from check_novelty import require

def minimize(rows,loose):
    n=len(rows)//2;colors=[0]*n
    for iteration in range(n+1):
        labels={};out=[]
        for q in range(n):
            sig=[]
            for w,d,t in rows[2*q:2*q+2]:
                sig.extend((0 if loose and t<0 else w,'R' if loose and t<0 else d,-1 if t<0 else colors[t]))
            key=tuple(sig)
            if key not in labels:labels[key]=len(labels)
            out.append(labels[key])
        if out==colors:return len(labels),iteration
        colors=out
    raise ValueError('partition refinement failed to stabilize')

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    here=Path(__file__).resolve().parent;index=json.loads(gzip.decompress((here/'frontier194_index.json.gz').read_bytes()))
    expected={r['action_graph_sha256']:r for r in csv.DictReader((here/'congruence194.csv').open())};result=[]
    for c in index['classes']:
        a,ai=minimize(c['rows'],False);b,bi=minimize(c['rows'],True);old=expected[c['action_graph_sha256']]
        require((a,ai,b,bi)==tuple(int(old[k]) for k in ('exact_output_congruence_states','refinement_rounds_exact','ignore_final_action_congruence_states','refinement_rounds_loose')),'refinement receipt mismatch')
        result.append((a,b))
    out={'passed':True,'classes':len(result),'exact_histogram':dict(Counter(a for a,b in result)),'loose_histogram':dict(Counter(b for a,b in result)),
         'scope':'Restricted action/target congruence only; no general TM state lower bound.'}
    args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()
