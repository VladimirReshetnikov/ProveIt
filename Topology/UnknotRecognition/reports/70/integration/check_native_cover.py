#!/usr/bin/env python3
"""Optional cross-check against the maintained ProveIt surface-cover API.

Usage: python integration/check_native_cover.py /path/to/ProveIt
This script was NOT run for the delivered package: a local repository checkout
was not available. It compares component counts, not full surface topology.
"""
from pathlib import Path
import json
import random
import sys
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'src'))
from affine_orbits import BulkIndex, Model, Edge


def main():
    if len(sys.argv) != 2:
        raise SystemExit('usage: check_native_cover.py /path/to/ProveIt')
    native = Path(sys.argv[1]).resolve()/'Topology/UnknotRecognition/fast'
    if not (native/'fastunknot/surface_cover.py').is_file():
        raise SystemExit(f'missing maintained module: {native}')
    sys.path.insert(0,str(native))
    from fastunknot.surface_cover import CoverIndex
    rng=random.Random(261009708)
    checked=0
    for W in (1,2,3,8,12,64,1<<1024):
        for rank in range(4):
            for _ in range(8):
                maps=[dict(sign=rng.choice((-1,1)),shift=rng.randrange(W)) for _ in range(rank)]
                supplied=dict(surface=dict(orientable=True,genus=0,boundary_components=rank+1),
                              sheets=W,monodromy=maps)
                result=CoverIndex(supplied).summary
                ours=BulkIndex(Model(1,W,1,tuple(Edge(0,0,x['sign'],x['shift']) for x in maps)))
                assert result['component_count']==ours.component_count
                checked+=1
    print(json.dumps(dict(status='PASS',component_count_comparisons=checked)))

if __name__=='__main__':main()
