"""Recognize or replay a binary Artin braid grammar without expanding it."""
import argparse
import json
from pathlib import Path

from . import recognize, verify, CompressedLimit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('recognize', 'verify'))
    parser.add_argument('input', type=Path)
    parser.add_argument('--certificate', type=Path)
    parser.add_argument('--max-nodes', type=int, default=100000)
    parser.add_argument('--max-work', type=int, default=10000000)
    parser.add_argument('--max-input-rules', type=int, default=100000)
    parser.add_argument('--max-input-bytes', type=int, default=16000000)
    parser.add_argument('--max-certificate-bytes', type=int, default=64000000)
    parser.add_argument('--seconds', type=float)
    parser.add_argument('--fallback-max-crossings', type=int, default=12)
    parser.add_argument('--fallback-max-generators', type=int, default=200000)
    parser.add_argument('--no-fallback-reduction', action='store_true')
    parser.add_argument('--eager-factors', action='store_true')
    args = parser.parse_args()
    if args.action == 'verify' and args.certificate is None:
        parser.error('verify requires --certificate')
    if args.max_input_bytes < 0 or args.max_certificate_bytes < 0:
        parser.error('byte allowances must be nonnegative')

    def load(path, limit):
        with path.open('rb') as stream:
            raw = stream.read(limit + 1)
        if len(raw) > limit:
            raise CompressedLimit('serialized input exceeds its byte allowance')
        return json.loads(raw)

    options = {key: getattr(args, key) for key in ('max_nodes', 'max_work', 'max_input_rules',
               'max_input_bytes', 'max_certificate_bytes', 'seconds',
               'fallback_max_crossings', 'fallback_max_generators')}
    try:
        data = load(args.input, args.max_input_bytes)
        if args.action == 'recognize':
            result = recognize(data, use_fallback_reduction=not args.no_fallback_reduction,
                               use_lazy_factors=not args.eager_factors, **options)
        else:
            cert = load(args.certificate, args.max_certificate_bytes)
            if isinstance(cert, dict):
                cert = cert.get('certificate', cert)
            result = dict(status=verify(data, cert, **options), verified=True)
    except CompressedLimit as exc:
        result = dict(status='INCONCLUSIVE', reason=str(exc))
    except (ValueError, TypeError) as exc:
        result = dict(status='INVALID', reason=str(exc))
    print(json.dumps(result, sort_keys=True))
    return 2 if result['status'] == 'INVALID' else 3 if result['status'] == 'INCONCLUSIVE' else 0


if __name__ == '__main__':
    raise SystemExit(main())
