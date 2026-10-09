"""Command-line finite-language solver. Status strings never assert unknotting."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
from .assembly import Grammar, solve
from .kernel import Candidate, State, ResourceLimit
from .mesh import replay_assignment
from .verify import verify_reduction
from .search_verify import verify_search


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, help='rooted-patch-language-v1 JSON file')
    parser.add_argument('--exact', action='store_true', help='use full exact-state tables, without basis reduction')
    parser.add_argument('--check', action='store_true', help='independently check reduction evidence and mesh witness')
    parser.add_argument('--max-transitions', type=int)
    parser.add_argument('--max-dimension', type=int, default=2_000_000)
    parser.add_argument('--output', type=Path, help='write detailed answer JSON here')
    args = parser.parse_args()
    try:
        grammar = Grammar.from_dict(json.loads(args.input.read_text(encoding='utf-8')))
        answer = solve(grammar, reduced=not args.exact, certificates=args.check,
                       max_transitions=args.max_transitions, max_dimension=args.max_dimension)
        payload = answer.as_dict()
        if args.check:
            if not args.exact:
                if not verify_search(grammar, payload, max_dimension=args.max_dimension):
                    raise ValueError('independent complete-language replay rejected the search')
                payload['complete_language_checked'] = True
            for record in answer.reductions:
                family = [Candidate(State.from_dict(x['state']), int(x['cost'], 16), tuple(x['witness']))
                          for x in record['candidates']]
                cert = record['certificate']
                if not verify_reduction(family, cert, geometry_key=cert['geometry_key'], max_dimension=args.max_dimension):
                    raise ValueError('independent algebraic replay rejected the reduction')
            payload['algebra_checked'] = True
            if answer.witness is not None:
                mesh = replay_assignment(grammar, answer.witness)
                if not mesh.succeeds(grammar.target) or mesh.cost != answer.cost:
                    raise ValueError('independent mesh replay rejected the answer')
                payload['mesh_checked'] = True
                payload['root_euler'] = mesh.root_euler
                payload['root_charge'] = mesh.root_charge
                payload['mesh_triangles'] = mesh.triangles
                payload['component_summary'] = mesh.components
        text = json.dumps(payload, indent=2) + '\n'
        if args.output:
            args.output.write_text(text, encoding='utf-8')
            brief = {k:v for k,v in payload.items() if k != 'reductions'}
            print(json.dumps(brief, indent=2))
        else:
            print(text, end='')
        return 0
    except ResourceLimit as exc:
        print(json.dumps({'status': 'INCONCLUSIVE_RESOURCE_LIMIT', 'detail': str(exc)}))
        return 2
    except (ValueError, TypeError, KeyError, OSError, IndexError) as exc:
        print(json.dumps({'status': 'INVALID_INPUT_OR_REPLAY', 'detail': str(exc)}), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
