from __future__ import annotations
import argparse
import json
import sys
from . import Instance, solve, verify_positive, verify_obstruction


def main() -> int:
    parser = argparse.ArgumentParser(description='Certified local dual-forest research kernel; not an unknot recognizer.')
    parser.add_argument('input')
    parser.add_argument('--rounds', type=int, default=8)
    parser.add_argument('--seed', type=int, default=None, help='fixed PRNG seed for reproduction, not derandomization')
    parser.add_argument('--max-b', type=int, default=20)
    parser.add_argument('--max-transitions', type=int, default=1000000)
    parser.add_argument('--no-incumbent', action='store_true')
    parser.add_argument('--verify', metavar='RESULT_JSON')
    args = parser.parse_args()
    try:
        with open(args.input, encoding='utf-8') as handle:
            inst = Instance.from_dict(json.load(handle))
        if args.verify:
            with open(args.verify, encoding='utf-8') as handle:
                ans = json.load(handle)
            ok = ((ans.get('status') == 'SUCCESS' and verify_positive(inst, ans.get('certificate')))
                  or (ans.get('status') == 'BLOCKED_EXACT' and verify_obstruction(inst, ans.get('obstruction'))))
            print(json.dumps(dict(verified=ok, scope='fixed local matrix/graph only')))
            return 0 if ok else 1
        answer = solve(inst, rounds=args.rounds, seed=args.seed, max_b=args.max_b,
                       max_transitions=args.max_transitions, try_incumbent=not args.no_incumbent)
        print(json.dumps(answer, indent=2))
        return 0
    except (ValueError, TypeError, KeyError, OSError) as error:
        print(str(error), file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
