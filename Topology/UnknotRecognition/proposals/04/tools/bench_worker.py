"""One isolated timing sample; called by benchmark.py (standard library only)."""
from __future__ import annotations
import argparse
import gc
import importlib
import json
import sys
import time
import tracemalloc
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def main():
    p = argparse.ArgumentParser()
    p.add_argument('implementation', choices=['baseline', 'fast'])
    p.add_argument('operation', choices=['recognize', 'scan', 'factored', 'jones', 'order'])
    p.add_argument('input')
    p.add_argument('--seconds', type=float, default=60.0)
    p.add_argument('--memory', action='store_true')
    p.add_argument('--pivot-strategy', choices=['minfill','stack'], default='minfill')
    args = p.parse_args()
    sys.path.insert(0, str(ROOT / args.implementation))
    from fastunknot.diagram import Diagram
    from fastunknot.scan import ScanLimit, khovanov_rank, best_scan_order
    from fastunknot.recognize import recognize
    diagram = Diagram.from_json(json.loads(Path(args.input).read_text()))
    # Imports and JSON/Diagram construction are deliberately outside the timer.
    # Process creation is outside too; a fresh process makes caches cold.
    if args.operation == 'factored':
        from fastunknot.factor import factored_khovanov_rank
    if args.operation == 'jones':
        from fastunknot.jones import bracket_evaluation
    if args.memory:
        tracemalloc.start()
    started = time.perf_counter()
    try:
        if args.operation == 'recognize':
            r = recognize(diagram, seconds=args.seconds)
            result = r.to_json()
            status = r.status
        elif args.operation == 'scan':
            options = {'pivot_strategy': args.pivot_strategy} if args.implementation == 'fast' else {}
            result = khovanov_rank(diagram.pd, seconds=args.seconds, **options)
            status = 'OK'
        elif args.operation == 'factored':
            result = factored_khovanov_rank(diagram, seconds=args.seconds)
            status = 'OK'
        elif args.operation == 'jones':
            result = bracket_evaluation(diagram, seconds=args.seconds).to_json()
            status = 'OK'
        else:
            result = best_scan_order(list(diagram.pd), tries=min(12, diagram.crossings))
            status = 'OK'
    except (ScanLimit, MemoryError) as exc:
        result = {'reason': str(exc) or 'memory allocation failed'}
        status = 'LIMIT'
    elapsed = time.perf_counter() - started
    peak = tracemalloc.get_traced_memory()[1] if args.memory else None
    print(json.dumps({'implementation': args.implementation, 'operation': args.operation,
                      'input': Path(args.input).name, 'crossings': diagram.crossings,
                      'status': status, 'wall_seconds': elapsed,
                      'peak_python_bytes': peak, 'result': result}))

if __name__ == '__main__':
    main()
