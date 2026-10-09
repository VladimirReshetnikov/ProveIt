import argparse
import json
from pathlib import Path
from . import recognize, verify, Limit
from .forest import recognize_forest, verify_forest


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('action', choices=['recognize', 'verify', 'forest', 'verify-forest'])
    p.add_argument('input', type=Path)
    p.add_argument('--certificate', type=Path)
    p.add_argument('--output', type=Path)
    p.add_argument('--max-nodes', type=int, default=1000000)
    p.add_argument('--max-work', type=int, default=50000000)
    args = p.parse_args()
    data = json.loads(args.input.read_text())
    options = dict(max_nodes=args.max_nodes, max_work=args.max_work)
    try:
        if args.action in ('recognize', 'forest'):
            producer = recognize if args.action == 'recognize' else recognize_forest
            checker = verify if args.action == 'recognize' else verify_forest
            result = producer(data, **options)
            checker(data, result['certificate'], **options)
        else:
            if args.certificate is None:
                p.error('verify requires --certificate')
            cert = json.loads(args.certificate.read_text())
            cert = cert.get('certificate', cert)
            checker = verify if args.action == 'verify' else verify_forest
            result = dict(status=checker(data, cert, **options), verified=True)
    except Limit as exc:
        result = dict(status='INCONCLUSIVE', reason=str(exc))
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end='')

if __name__ == '__main__':
    main()
