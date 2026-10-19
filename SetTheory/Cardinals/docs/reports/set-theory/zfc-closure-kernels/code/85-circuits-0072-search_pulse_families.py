#!/usr/bin/env python3
"""New finite pulse-removal families, extending the prior bounded scope.

The original source is loaded without edits; its fixtures and endpoint semantics
are retained. Results are finite synthesis diagnostics, not a lower bound.
"""
from pathlib import Path
import argparse, json
from common import OUTPUT
import pulse_primitives as prior
FAMILIES=[
    [(75,0),(83,0)],
    [(75,0),(83,1)],
    [(75,0),(73,0)],
    [(75,0),(73,1)],
    [(75,0),(48,0)],
    [(75,0),(48,1)],
    [(75,0),(63,0)],
    [(75,0),(63,1)],
    [(75,0),(83,0),(131,0)],
    [(75,0),(83,0),(131,1)],
    [(75,0),(83,0),(112,0)],
    [(75,0),(83,0),(112,1)],
    [(75,0),(83,0),(75,1)],
    [(75,0),(83,0),(109,0)],
    [(75,0),(83,0),(109,1)],
    [(75,0),(83,0),(73,0)],
    [(75,0),(83,0),(48,0)],
    [(75,0),(83,0),(63,0)],
    [(75,0),(83,0),(131,0),(131,1)],
    [(75,0),(83,0),(112,0),(112,1)],
    [(75,0),(83,0),(73,0),(73,1)],
]
if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-only', action='store_true')
    parser.add_argument('--output',type=Path,default=OUTPUT/'pulse-families.json')
    args=parser.parse_args()
    assert __debug__, 'Assertions required; do not use -O.'
    T=prior.table();cases=list(prior.fixtures(False));prior.check_baseline(T,cases)
    assert len(cases)==48
    if args.baseline_only:
        print('48 exact full-tape baseline fixtures PASS')
    else:
        out=dict(status='COMPLETE',scope='Finite synthesis; ticks1 through249 only.',
            deleted_state=255,actions_per_hole=100,fixture_count=48,
            recipe_domain_sum=sum(100**len(f) for f in FAMILIES),families=[])
        for fam in FAMILIES:
            result=prior.search(T,cases,fam);out['families'].append(result)
            print(json.dumps(result),flush=True)
            args.output.parent.mkdir(parents=True,exist_ok=True)
            args.output.write_text(json.dumps(out,indent=2)+'\n')
