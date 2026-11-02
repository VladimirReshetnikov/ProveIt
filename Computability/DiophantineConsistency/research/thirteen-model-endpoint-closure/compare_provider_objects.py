#!/usr/bin/env python3
"""Compare retained current model-view project objects with historical ones."""
import hashlib,json,os,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('reject optimized Python')
HERE=Path(__file__).resolve().parent
VIEW=Path('/tmp/ipra-thirteen-model-view-pair-01')
PAIR=Path('/tmp/ipra-aq29-fresh-project-pair')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    result={}
    for side in ('author','peer'):
        current=VIEW/side/'lib';history=PAIR/side/'lib';rows=[]
        for p in sorted(current.rglob('*.olean')):
            q=history/p.relative_to(current)
            if q.is_file():
                rows.append({'module':'.'.join(p.relative_to(current).with_suffix('').parts),'current_path':str(p),'current_sha256':H(p),'historical_path':str(q),'historical_sha256':H(q)})
        result[side]=rows
    if [(r['module'],r['current_sha256'],r['historical_sha256']) for r in result['author']]!=[(r['module'],r['current_sha256'],r['historical_sha256']) for r in result['peer']]:raise ValueError('sibling comparison differs')
    mismatches=[r['module'] for r in result['author'] if r['current_sha256']!=r['historical_sha256']]
    out={'status':'CURRENT_HISTORICAL_PROJECT_OBJECT_COMPARISON_NOT_A_BUILD','per_side_overlap':len(result['author']),
         'per_side_differing':len(mismatches),'different_modules':mismatches,'rows':result,
         'scope':'Point-in-time object-byte comparison; no assertion that matching source or hashes authenticates a mixed-generation import closure.'}
    path=HERE/'provider-object-comparison.json'
    if sys.argv[1:]==['--check']:
        if json.loads(path.read_text())!=out:raise ValueError('provider comparison mismatch')
    elif not sys.argv[1:]:
        if path.exists():raise ValueError('refusing overwrite')
        path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    else:raise ValueError('use no arguments or --check')
    print('PASS_PROVIDER_OBJECT_COMPARISON',len(result['author']),'different',len(mismatches))
if __name__=='__main__':main()
