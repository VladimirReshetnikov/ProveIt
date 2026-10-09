"""Analyze supplied interval relations or independently check a certificate."""
import argparse
from pathlib import Path
from . import codec
from .api import analyze
from .verify import verify

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    run = sub.add_parser('analyze')
    run.add_argument('input', type=Path)
    run.add_argument('--output', type=Path, required=True)
    run.add_argument('--strategy', choices=('flat','balanced'), default='balanced')
    run.add_argument('--certificate', action='store_true')
    run.add_argument('--max-cycles', type=int)
    run.add_argument('--max-queries', type=int)
    run.add_argument('--max-entries', type=int)
    check = sub.add_parser('verify')
    check.add_argument('input', type=Path)
    check.add_argument('result', type=Path)
    args = parser.parse_args()
    source = codec.load(args.input)
    if args.action == 'analyze':
        result = analyze(source['size'], source['pairings'], source['ports'],
            strategy=args.strategy, record_certificate=args.certificate,
            max_cycles=args.max_cycles, max_queries=args.max_queries,
            max_entries=args.max_entries)
        codec.save(args.output, result)
        print(result['status'])
        return 0 if result['status'] == 'COMPLETE' else 2
    result = codec.load(args.result)
    accepted = verify(source['size'], source['pairings'], source['ports'], result.get('certificate'))
    print('VERIFIED INCIDENCE' if accepted else 'INVALID CERTIFICATE')
    return 0 if accepted else 1

if __name__ == '__main__':
    raise SystemExit(main())
