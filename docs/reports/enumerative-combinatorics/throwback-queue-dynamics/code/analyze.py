"""Command-line first-obstruction analysis; no third-party dependencies."""
from __future__ import annotations
import argparse
import json
from throwback import first_obstruction, sorted_statistics, certified_orbit


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('weights', type=int, nargs='+', help='Positive weights in original order.')
    parser.add_argument('--simulate', action='store_true', help='Also generate the exact transient and period.')
    parser.add_argument('--max-steps', type=int, default=1000000,
                        help='Resource cap for optional simulation (default: 1000000).')
    args = parser.parse_args()
    if any(x <= 0 for x in args.weights) or args.max_steps <= 0:
        parser.error('Weights and --max-steps must be positive integers.')
    cert = first_obstruction(args.weights)
    if cert is None:
        print(json.dumps({'status': 'inspected prefix is admissible',
                          'inspected_tokens': len(args.weights),
                          'scope': 'This does not certify any unspecified infinite continuation.'}, indent=2))
        return
    if not cert.verify():
        raise AssertionError('Independent certificate verification failed.')
    stats = sorted_statistics(cert.core_weights, closed=True)
    labels = sorted(cert.core_labels, key=lambda i: (cert.prefix[i], i))
    result = {'status': 'finite obstruction certified',
              'first_bad_index': cert.first_bad_index,
              'least_overloaded_threshold': cert.threshold,
              'labels_that_ever_lead': list(range(cert.first_bad_index + 1)),
              'recurrent_labels': cert.core_labels,
              'recurrent_weights': cert.core_weights,
              'labeled_period': stats['period'],
              'labeled_frequencies': {i: str(f) for i, f in zip(labels, stats['frequencies'])},
              'scope': 'Valid for every positive infinite continuation of the certified prefix.'}
    if args.simulate:
        try:
            result['orbit'] = certified_orbit(cert, args.max_steps)
        except TimeoutError as exc:
            result['simulation_status'] = str(exc)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
