from __future__ import annotations
import argparse
import json
from pathlib import Path
from .kernel import compress
from .verify import verify


def main() -> None:
    parser = argparse.ArgumentParser(description='Certified rank-two braid shortening')
    sub = parser.add_subparsers(dest='command', required=True)
    comp = sub.add_parser('compress')
    comp.add_argument('input', type=Path)
    comp.add_argument('--output', type=Path)
    comp.add_argument('--radius', type=int, choices=(0, 1), default=1)
    comp.add_argument('--dictionary', choices=('avl', 'hash'), default='avl')
    comp.add_argument('--passes', type=int, default=None)
    ver = sub.add_parser('verify')
    ver.add_argument('input', type=Path)
    ver.add_argument('result', type=Path)
    args = parser.parse_args()
    try:
        data = json.loads(args.input.read_text())
        if args.command == 'compress':
            result = compress(data['strands'], data['word'], radius=args.radius,
                              max_passes=args.passes, dictionary=args.dictionary)
            # Never publish an optimizer output without replaying its certificate.
            verify(data['strands'], data['word'], result['certificate'])
        else:
            data_result = json.loads(args.result.read_text())
            output, statistics = verify(data['strands'], data['word'], data_result['certificate'])
            result = {'same_braid_verified': True, 'output_word': list(output), 'stats': statistics}
        text = json.dumps(result, indent=2) + '\n'
        if args.command == 'compress' and args.output is not None:
            args.output.write_text(text)
        else:
            print(text, end='')
    except (ValueError, KeyError, TypeError, OSError) as exc:
        parser.exit(2, f'error: {exc}\n')


if __name__ == '__main__':
    main()
