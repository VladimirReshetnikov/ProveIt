from __future__ import annotations
import argparse
from dataclasses import asdict
import json
from pathlib import Path
from . import Diagram, probe, adaptive_probe

def main():
    p = argparse.ArgumentParser(description='Exact endpoint homology probe; UNKNOWN is not an unknot verdict.')
    p.add_argument('input', type=Path)
    p.add_argument('--depth', type=int, default=2)
    p.add_argument('--adaptive', action='store_true')
    p.add_argument('--max-objects', type=int, default=20000)
    p.add_argument('--seconds', type=float, default=60)
    args = p.parse_args()
    try:
        data = json.loads(args.input.read_text())
        if 'braid' in data:
            d = Diagram.from_braid(data['braid']['strands'], data['braid']['word'])
        else:
            d = Diagram.from_pd(data['pd'])
        kw = dict(max_objects=args.max_objects, seconds=args.seconds)
        r = adaptive_probe(d, **kw) if args.adaptive else probe(d, args.depth, **kw)
        print(json.dumps(asdict(r), indent=2, sort_keys=True))
    except (ValueError, KeyError, OSError) as exc:
        p.error(str(exc))

if __name__ == '__main__':
    main()
