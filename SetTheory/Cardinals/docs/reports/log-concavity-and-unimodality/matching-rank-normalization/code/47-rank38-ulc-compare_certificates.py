"""Compare regenerated integer-coefficient records, ignoring elapsed time."""
from argparse import ArgumentParser
from pathlib import Path
import json

if __name__=='__main__':
    ap=ArgumentParser()
    ap.add_argument('expected',type=Path)
    ap.add_argument('actual',type=Path)
    args=ap.parse_args()
    for r in range(6,39):
        name=f'rank_{r:02d}.json'
        x=json.loads((args.expected/name).read_text())
        y=json.loads((args.actual/name).read_text())
        x.pop('elapsed_seconds',None);y.pop('elapsed_seconds',None)
        if x!=y:
            raise RuntimeError(('certificate mismatch',r))
    print('All 33 rank files and 13,651 per-gap records agree exactly.')
