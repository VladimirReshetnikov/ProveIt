"""Command-line interface; accepts braid words or signed run pairs, not PD codes."""
from __future__ import annotations
import argparse
import json
import sys
from pathlib import Path
from .preflight import basis_size, generator_basis_bound, degree_profile
from .core import Budget, Run, ResourceLimit, homology, recognize, runs_from_word, size_estimate, validate_runs


def load_braid(value: dict):
    if not isinstance(value, dict):
        raise ValueError('input must be a JSON object')
    data = value.get('braid', value)
    if not isinstance(data, dict) or 'strands' not in data:
        raise ValueError('expected braid.strands; PD and grid inputs are not supported')
    b = data['strands']
    if ('word' in data) == ('runs' in data):
        raise ValueError('provide exactly one of word or runs')
    if 'word' in data:
        return b, runs_from_word(b, data['word'])
    if not isinstance(data['runs'], list) or any(not isinstance(r, list) or len(r) != 2 for r in data['runs']):
        raise ValueError('runs must be [generator, signed_exponent] pairs')
    return b, validate_runs(b, (Run(*r) for r in data['runs']))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--mode', choices=('recognize', 'homology', 'estimate'), default='recognize')
    parser.add_argument('--check-d2', action='store_true')
    parser.add_argument('--profile', action='store_true',help='also compute exact chain dimensions in estimate mode')
    for name, default in [('max-states',250000),('max-basis',1000000),
                          ('max-matrix-bits',1000000000),('max-xors',20000000)]:
        parser.add_argument('--'+name, type=int, default=default)
    parser.add_argument('--seconds', type=float)
    args=parser.parse_args(argv)
    try:
        b, runs = load_braid(json.loads(args.input.read_text()))
        if args.mode == 'estimate':
            result = size_estimate(b, runs, max_supports=0)
            try:
                result['generator_basis_bound'] = generator_basis_bound(b,runs)
                result['temperley_lieb'] = basis_size(b,runs)
                if args.profile: result['dimension_profile'] = degree_profile(b,runs)
            except ResourceLimit as exc:
                result['preflight_limit'] = str(exc)
        else:
            budget=Budget(args.max_states,args.max_basis,args.max_matrix_bits,args.max_xors,args.seconds)
            fn=recognize if args.mode=='recognize' else homology
            result=fn(b,runs,budget=budget,check_d2=args.check_d2)
    except (OSError, ValueError, TypeError) as exc:
        print(json.dumps({'status':'INVALID','reason':str(exc)}))
        return 2
    except (ResourceLimit, MemoryError) as exc:
        print(json.dumps({'status':'UNKNOWN','reason':str(exc)}))
        return 3
    print(json.dumps(result, indent=2, sort_keys=True))
    return 3 if result.get('status') == 'UNKNOWN' else 0

if __name__ == '__main__':
    sys.exit(main())

