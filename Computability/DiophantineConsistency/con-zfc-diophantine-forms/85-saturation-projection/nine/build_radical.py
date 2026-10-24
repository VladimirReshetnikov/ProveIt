#!/usr/bin/env python3
"""Choose the cheapest of24 exact multivariate Horner orders."""
import itertools,json
from pathlib import Path
from build import build
ROOT=Path(__file__).resolve().parent
def main():
    options=[build('positive','radical',o) for o in itertools.permutations(range(4))]
    winner=min(options,key=lambda r:(r['total_operations'],r['horner_order']))
    order=winner['horner_order'];rows=[]
    for domain in ['positive','natural']:
        obj=build(domain,'radical',order)
        (ROOT/('saturated_radical_'+domain+'.json')).write_text(json.dumps(obj,indent=2)+'\n')
        rows.append({k:obj[k] for k in ['domain','exact_degree','total_operations','operation_counts','horner_order']})
    (ROOT/'RADICAL_METRICS.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps(rows,indent=2))
if __name__=='__main__':main()
